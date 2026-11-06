import NetHack.Soko22Hazard87.AndIntroBlocks0033
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro8500 (p : Pattern) (ha : d69955 p = 1) (hb : d77845 p = 1) : d80546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69950 q = 1) (hb : d77845 q = 1) : d80541 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d69950, d80541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8499 q ha hb
    | true =>
      simp only [d69950, d80541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69951 q = 1) (hb : d77845 q = 1) : d80542 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d69951, d80542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69951, d80542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69952 q = 1) (hb : d77845 q = 1) : d80543 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d69952, d80543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69952, d80543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69953 q = 1) (hb : d77845 q = 1) : d80544 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d69953, d80544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69953, d80544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69954 q = 1) (hb : d77845 q = 1) : d80545 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d69954, d80545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69954, d80545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69955 q = 1) (hb : d77845 q = 1) : d80546 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d69955, d80546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69955, d80546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8501 (p : Pattern) (ha : d69961 p = 1) (hb : d77845 p = 1) : d80552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69956 q = 1) (hb : d77845 q = 1) : d80547 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d69956, d80547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8500 q ha hb
    | true =>
      simp only [d69956, d80547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69957 q = 1) (hb : d77845 q = 1) : d80548 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d69957, d80548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69957, d80548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69958 q = 1) (hb : d77845 q = 1) : d80549 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d69958, d80549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69958, d80549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69959 q = 1) (hb : d77845 q = 1) : d80550 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d69959, d80550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69959, d80550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69960 q = 1) (hb : d77845 q = 1) : d80551 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d69960, d80551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69960, d80551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69961 q = 1) (hb : d77845 q = 1) : d80552 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d69961, d80552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69961, d80552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8502 (p : Pattern) (ha : d69967 p = 1) (hb : d77845 p = 1) : d80558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69962 q = 1) (hb : d77845 q = 1) : d80553 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d69962, d80553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8501 q ha hb
    | true =>
      simp only [d69962, d80553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69963 q = 1) (hb : d77845 q = 1) : d80554 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d69963, d80554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69963, d80554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69964 q = 1) (hb : d77845 q = 1) : d80555 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d69964, d80555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69964, d80555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69965 q = 1) (hb : d77845 q = 1) : d80556 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d69965, d80556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69965, d80556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69966 q = 1) (hb : d77845 q = 1) : d80557 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d69966, d80557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69966, d80557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69967 q = 1) (hb : d77845 q = 1) : d80558 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d69967, d80558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69967, d80558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8503 (p : Pattern) (ha : d78885 p = 1) (hb : d79700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78867 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78873 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78880 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78801 q = 1) (hb : d79652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78801, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8326 q ha hb
    | true =>
      simp only [d78801, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d78881 q = 1) (hb : d79696 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78881, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d78881, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d78802 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d78882 q = 1) (hb : d79697 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78882, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78882, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d78883 q = 1) (hb : d79698 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78883, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d78883, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d78884 q = 1) (hb : d79699 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78884, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d78884, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d78885 q = 1) (hb : d79700 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78885, d79700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78885, d79700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8504 (p : Pattern) (ha : d78901 p = 1) (hb : d79707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78867 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78873 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78880 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78801 q = 1) (hb : d79652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78801, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8326 q ha hb
    | true =>
      simp only [d78801, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78881 q = 1) (hb : d79696 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78881, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d78881, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d78802 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d78882 q = 1) (hb : d79697 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78882, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78882, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d78883 q = 1) (hb : d79698 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78883, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d78883, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d78884 q = 1) (hb : d79699 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78884, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78884, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d78890 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d78894 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d78896 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d78808 q = 1) (hb : d79659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78808, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8328 q ha hb
    | true =>
      simp only [d78808, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d78897 q = 1) (hb : d79703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78897, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d78897, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d78809 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d78898 q = 1) (hb : d79704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78898, d79704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d78898, d79704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d78899 q = 1) (hb : d79705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78899, d79705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d78899, d79705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d78900 q = 1) (hb : d79706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78900, d79706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d78900, d79706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d78901 q = 1) (hb : d79707 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78901, d79707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d78901, d79707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8505 (p : Pattern) (ha : d78910 p = 1) (hb : d80353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78896 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d78808 q = 1) (hb : d79659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78808, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8328 q ha hb
    | true =>
      simp only [d78808, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d78897 q = 1) (hb : d79703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78897, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d78897, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d78809 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d78898 q = 1) (hb : d79704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78898, d79704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d78898, d79704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d78908 q = 1) (hb : d79705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78908, d79705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78908, d79705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78909 q = 1) (hb : d79706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78909, d79706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78909, d79706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d78910 q = 1) (hb : d80353 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78910, d80353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78910, d80353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8506 (p : Pattern) (ha : d78927 p = 1) (hb : d80363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78922 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d78830 q = 1) (hb : d79679 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78830, d79679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8332 q ha hb
    | true =>
      simp only [d78830, d79679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d78923 q = 1) (hb : d80359 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78923, d80359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d78923, d80359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d78831 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d78924 q = 1) (hb : d80360 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78924, d80360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d78924, d80360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d78925 q = 1) (hb : d80361 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78925, d80361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78925, d80361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78926 q = 1) (hb : d80362 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78926, d80362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78926, d80362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d78927 q = 1) (hb : d80363 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78927, d80363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78927, d80363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8507 (p : Pattern) (ha : d78933 p = 1) (hb : d80369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78861 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78902 q = 1) (hb : d79708 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78902, d79708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8503 q ha hb
    | true =>
      simp only [d78902, d79708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8504 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78904 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d78905 q = 1) (hb : d79709 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78905, d79709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d78905, d79709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d78906 q = 1) (hb : d80351 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78906, d80351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d78906, d80351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d78907 q = 1) (hb : d80352 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d78907, d80352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78907, d80352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78911 q = 1) (hb : d80354 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78911, d80354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d78911, d80354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8505 q ha hb
  have h8 (q : Pattern) (ha : d78912 q = 1) (hb : d80355 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78912, d80355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d78912, d80355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d78913 q = 1) (hb : d80356 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78913, d80356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d78913, d80356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d78914 q = 1) (hb : d80357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d78914, d80357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d78914, d80357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d78915 q = 1) (hb : d80358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d78915, d80358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78915, d80358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d78928 q = 1) (hb : d80364 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78928, d80364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d78928, d80364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8506 q ha hb
  have h13 (q : Pattern) (ha : d78929 q = 1) (hb : d80365 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78929, d80365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d78929, d80365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d78930 q = 1) (hb : d80366 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78930, d80366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d78930, d80366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d78931 q = 1) (hb : d80367 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d78931, d80367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d78931, d80367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d78932 q = 1) (hb : d80368 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d78932, d80368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d78932, d80368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d78933 q = 1) (hb : d80369 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d78933, d80369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d78933, d80369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8508 (p : Pattern) (ha : d78939 p = 1) (hb : d80375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78846 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d78934 q = 1) (hb : d80370 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d78934, d80370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d78934, d80370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8507 q ha hb
  have h3 (q : Pattern) (ha : d78935 q = 1) (hb : d80371 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d78935, d80371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d78935, d80371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78936 q = 1) (hb : d80372 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d78936, d80372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d78936, d80372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78937 q = 1) (hb : d80373 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d78937, d80373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d78937, d80373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78938 q = 1) (hb : d80374 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d78938, d80374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d78938, d80374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78939 q = 1) (hb : d80375 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d78939, d80375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78939, d80375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8509 (p : Pattern) (ha : d78994 p = 1) (hb : d79792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78969 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78975 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78988 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78946 q = 1) (hb : d79787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78946, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8353 q ha hb
    | true =>
      simp only [d78946, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d78989 q = 1) (hb : d79788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78989, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d78989, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d78990 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d78991 q = 1) (hb : d79789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78991, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78991, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d78992 q = 1) (hb : d79790 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78992, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d78992, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d78993 q = 1) (hb : d79791 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78993, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d78993, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d78994 q = 1) (hb : d79792 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78994, d79792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78994, d79792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8510 (p : Pattern) (ha : d79012 p = 1) (hb : d79801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78969 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78975 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78988 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78946 q = 1) (hb : d79787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78946, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8353 q ha hb
    | true =>
      simp only [d78946, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78989 q = 1) (hb : d79788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78989, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d78989, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d78990 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d78991 q = 1) (hb : d79789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78991, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78991, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d78992 q = 1) (hb : d79790 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78992, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d78992, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d78993 q = 1) (hb : d79791 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78993, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78993, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d78999 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d79003 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d79006 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d78955 q = 1) (hb : d79796 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78955, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8355 q ha hb
    | true =>
      simp only [d78955, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d79007 q = 1) (hb : d79797 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79007, d79797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d79007, d79797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d79008 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d79009 q = 1) (hb : d79798 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79009, d79798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d79009, d79798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d79010 q = 1) (hb : d79799 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79010, d79799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d79010, d79799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d79011 q = 1) (hb : d79800 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79011, d79800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d79011, d79800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d79012 q = 1) (hb : d79801 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79012, d79801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79012, d79801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8511 (p : Pattern) (ha : d79026 p = 1) (hb : d80378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79006 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d78955 q = 1) (hb : d79796 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78955, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8355 q ha hb
    | true =>
      simp only [d78955, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79007 q = 1) (hb : d79797 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79007, d79797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79007, d79797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d79008 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79009 q = 1) (hb : d79798 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79009, d79798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79009, d79798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79024 q = 1) (hb : d79799 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79024, d79799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79024, d79799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79025 q = 1) (hb : d79800 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79025, d79800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79025, d79800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79026 q = 1) (hb : d80378 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79026, d80378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79026, d80378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8512 (p : Pattern) (ha : d79057 p = 1) (hb : d80388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79044 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79051 q = 1) (hb : d79867 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79051, d79867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8370 q ha hb
    | true =>
      simp only [d79051, d79867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79052 q = 1) (hb : d80384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79052, d80384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79052, d80384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d79053 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79054 q = 1) (hb : d80385 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79054, d80385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79054, d80385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79055 q = 1) (hb : d80386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79055, d80386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79055, d80386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79056 q = 1) (hb : d80387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79056, d80387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79056, d80387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79057 q = 1) (hb : d80388 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79057, d80388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79057, d80388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8513 (p : Pattern) (ha : d79063 p = 1) (hb : d80394 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78963 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79013 q = 1) (hb : d79802 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79013, d79802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8509 q ha hb
    | true =>
      simp only [d79013, d79802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8510 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79020 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d79021 q = 1) (hb : d79803 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79021, d79803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79021, d79803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79022 q = 1) (hb : d80376 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79022, d80376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79022, d80376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79023 q = 1) (hb : d80377 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79023, d80377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79023, d80377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79027 q = 1) (hb : d80379 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79027, d80379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d79027, d80379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8511 q ha hb
  have h8 (q : Pattern) (ha : d79028 q = 1) (hb : d80380 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79028, d80380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79028, d80380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d79029 q = 1) (hb : d80381 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79029, d80381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d79029, d80381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d79030 q = 1) (hb : d80382 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79030, d80382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79030, d80382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d79031 q = 1) (hb : d80383 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79031, d80383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79031, d80383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d79058 q = 1) (hb : d80389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79058, d80389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d79058, d80389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8512 q ha hb
  have h13 (q : Pattern) (ha : d79059 q = 1) (hb : d80390 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79059, d80390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79059, d80390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d79060 q = 1) (hb : d80391 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79060, d80391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d79060, d80391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d79061 q = 1) (hb : d80392 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79061, d80392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d79061, d80392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d79062 q = 1) (hb : d80393 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79062, d80393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d79062, d80393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d79063 q = 1) (hb : d80394 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d79063, d80394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79063, d80394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8514 (p : Pattern) (ha : d79069 p = 1) (hb : d80400 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79064 q = 1) (hb : d80395 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d79064, d80395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79064, d80395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8513 q ha hb
  have h2 (q : Pattern) (ha : d79065 q = 1) (hb : d80396 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d79065, d80396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79065, d80396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79066 q = 1) (hb : d80397 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d79066, d80397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79066, d80397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79067 q = 1) (hb : d80398 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d79067, d80398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79067, d80398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79068 q = 1) (hb : d80399 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d79068, d80399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79068, d80399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79069 q = 1) (hb : d80400 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d79069, d80400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79069, d80400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8515 (p : Pattern) (ha : d79125 p = 1) (hb : d79895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79106 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79119 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79077 q = 1) (hb : d79890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79077, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8375 q ha hb
    | true =>
      simp only [d79077, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79120 q = 1) (hb : d79891 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79120, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d79120, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d79121 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d79122 q = 1) (hb : d79892 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79122, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79122, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d79123 q = 1) (hb : d79893 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79123, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d79123, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79124 q = 1) (hb : d79894 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79124, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79124, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79125 q = 1) (hb : d79895 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79125, d79895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79125, d79895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8516 (p : Pattern) (ha : d79143 p = 1) (hb : d79904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79106 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79119 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79077 q = 1) (hb : d79890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79077, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8375 q ha hb
    | true =>
      simp only [d79077, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79120 q = 1) (hb : d79891 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79120, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d79120, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d79121 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d79122 q = 1) (hb : d79892 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79122, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79122, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d79123 q = 1) (hb : d79893 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79123, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79123, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79124 q = 1) (hb : d79894 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79124, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79124, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d79130 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d79134 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d79137 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d79086 q = 1) (hb : d79899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79086, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8377 q ha hb
    | true =>
      simp only [d79086, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d79138 q = 1) (hb : d79900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79138, d79900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d79138, d79900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d79139 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d79140 q = 1) (hb : d79901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79140, d79901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d79140, d79901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d79141 q = 1) (hb : d79902 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79141, d79902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d79141, d79902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d79142 q = 1) (hb : d79903 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79142, d79903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d79142, d79903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d79143 q = 1) (hb : d79904 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79143, d79904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79143, d79904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8517 (p : Pattern) (ha : d79157 p = 1) (hb : d80404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79137 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79086 q = 1) (hb : d79899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79086, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8377 q ha hb
    | true =>
      simp only [d79086, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79138 q = 1) (hb : d79900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79138, d79900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79138, d79900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d79139 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79140 q = 1) (hb : d79901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79140, d79901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79140, d79901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79155 q = 1) (hb : d79902 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79155, d79902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79155, d79902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79156 q = 1) (hb : d79903 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79156, d79903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79156, d79903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79157 q = 1) (hb : d80404 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79157, d80404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79157, d80404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8518 (p : Pattern) (ha : d79188 p = 1) (hb : d80414 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79175 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79182 q = 1) (hb : d79970 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79182, d79970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8392 q ha hb
    | true =>
      simp only [d79182, d79970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79183 q = 1) (hb : d80410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79183, d80410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79183, d80410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d79184 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79185 q = 1) (hb : d80411 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79185, d80411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79185, d80411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79186 q = 1) (hb : d80412 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79186, d80412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79186, d80412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79187 q = 1) (hb : d80413 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79187, d80413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79187, d80413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79188 q = 1) (hb : d80414 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79188, d80414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79188, d80414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8519 (p : Pattern) (ha : d79194 p = 1) (hb : d80420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79094 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79144 q = 1) (hb : d79905 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79144, d79905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8515 q ha hb
    | true =>
      simp only [d79144, d79905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8516 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79151 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d79152 q = 1) (hb : d79906 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79152, d79906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79152, d79906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79153 q = 1) (hb : d80402 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79153, d80402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79153, d80402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79154 q = 1) (hb : d80403 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79154, d80403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79154, d80403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79158 q = 1) (hb : d80405 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79158, d80405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d79158, d80405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8517 q ha hb
  have h8 (q : Pattern) (ha : d79159 q = 1) (hb : d80406 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79159, d80406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79159, d80406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d79160 q = 1) (hb : d80407 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79160, d80407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d79160, d80407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d79161 q = 1) (hb : d80408 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79161, d80408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79161, d80408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d79162 q = 1) (hb : d80409 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79162, d80409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79162, d80409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d79189 q = 1) (hb : d80415 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79189, d80415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d79189, d80415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8518 q ha hb
  have h13 (q : Pattern) (ha : d79190 q = 1) (hb : d80416 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79190, d80416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79190, d80416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d79191 q = 1) (hb : d80417 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79191, d80417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d79191, d80417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d79192 q = 1) (hb : d80418 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79192, d80418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d79192, d80418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d79193 q = 1) (hb : d80419 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79193, d80419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d79193, d80419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d79194 q = 1) (hb : d80420 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d79194, d80420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79194, d80420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8520 (p : Pattern) (ha : d79200 p = 1) (hb : d80426 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79195 q = 1) (hb : d80421 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d79195, d80421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79195, d80421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8519 q ha hb
  have h2 (q : Pattern) (ha : d79196 q = 1) (hb : d80422 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d79196, d80422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79196, d80422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79197 q = 1) (hb : d80423 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d79197, d80423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79197, d80423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79198 q = 1) (hb : d80424 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d79198, d80424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79198, d80424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79199 q = 1) (hb : d80425 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d79199, d80425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79199, d80425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79200 q = 1) (hb : d80426 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d79200, d80426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79200, d80426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8521 (p : Pattern) (ha : d79257 p = 1) (hb : d79999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79232 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79238 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79251 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79209 q = 1) (hb : d79994 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79209, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8397 q ha hb
    | true =>
      simp only [d79209, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79252 q = 1) (hb : d79995 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79252, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d79252, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d79253 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d79254 q = 1) (hb : d79996 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79254, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79254, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d79255 q = 1) (hb : d79997 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79255, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d79255, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79256 q = 1) (hb : d79998 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79256, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79256, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79257 q = 1) (hb : d79999 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79257, d79999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79257, d79999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8522 (p : Pattern) (ha : d79275 p = 1) (hb : d80008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79232 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79238 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79251 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79209 q = 1) (hb : d79994 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79209, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8397 q ha hb
    | true =>
      simp only [d79209, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79252 q = 1) (hb : d79995 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79252, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d79252, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d79253 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d79254 q = 1) (hb : d79996 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79254, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79254, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d79255 q = 1) (hb : d79997 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79255, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79255, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79256 q = 1) (hb : d79998 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79256, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79256, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d79262 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d79266 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d79269 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d79218 q = 1) (hb : d80003 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79218, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8399 q ha hb
    | true =>
      simp only [d79218, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d79270 q = 1) (hb : d80004 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79270, d80004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d79270, d80004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d79271 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d79272 q = 1) (hb : d80005 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79272, d80005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d79272, d80005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d79273 q = 1) (hb : d80006 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79273, d80006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d79273, d80006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d79274 q = 1) (hb : d80007 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79274, d80007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d79274, d80007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d79275 q = 1) (hb : d80008 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79275, d80008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79275, d80008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8523 (p : Pattern) (ha : d79289 p = 1) (hb : d80431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79218 q = 1) (hb : d80003 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79218, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8399 q ha hb
    | true =>
      simp only [d79218, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79270 q = 1) (hb : d80004 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79270, d80004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79270, d80004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d79271 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79272 q = 1) (hb : d80005 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79272, d80005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79272, d80005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79287 q = 1) (hb : d80006 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79287, d80006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79287, d80006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79288 q = 1) (hb : d80007 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79288, d80007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79288, d80007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79289 q = 1) (hb : d80431 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79289, d80431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79289, d80431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8524 (p : Pattern) (ha : d79320 p = 1) (hb : d80441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79307 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79314 q = 1) (hb : d80074 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79314, d80074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8414 q ha hb
    | true =>
      simp only [d79314, d80074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79315 q = 1) (hb : d80437 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79315, d80437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79315, d80437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d79316 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79317 q = 1) (hb : d80438 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79317, d80438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79317, d80438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79318 q = 1) (hb : d80439 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79318, d80439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79318, d80439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79319 q = 1) (hb : d80440 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79319, d80440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79319, d80440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79320 q = 1) (hb : d80441 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79320, d80441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79320, d80441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8525 (p : Pattern) (ha : d79326 p = 1) (hb : d80447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79226 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79276 q = 1) (hb : d80009 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79276, d80009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8521 q ha hb
    | true =>
      simp only [d79276, d80009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8522 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79283 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d79284 q = 1) (hb : d80010 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79284, d80010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79284, d80010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79285 q = 1) (hb : d80429 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79285, d80429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79285, d80429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79286 q = 1) (hb : d80430 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79286, d80430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79286, d80430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79290 q = 1) (hb : d80432 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79290, d80432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d79290, d80432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8523 q ha hb
  have h8 (q : Pattern) (ha : d79291 q = 1) (hb : d80433 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79291, d80433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79291, d80433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d79292 q = 1) (hb : d80434 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79292, d80434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d79292, d80434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d79293 q = 1) (hb : d80435 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79293, d80435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79293, d80435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d79294 q = 1) (hb : d80436 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79294, d80436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79294, d80436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d79321 q = 1) (hb : d80442 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79321, d80442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d79321, d80442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8524 q ha hb
  have h13 (q : Pattern) (ha : d79322 q = 1) (hb : d80443 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79322, d80443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79322, d80443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d79323 q = 1) (hb : d80444 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79323, d80444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d79323, d80444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d79324 q = 1) (hb : d80445 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79324, d80445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d79324, d80445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d79325 q = 1) (hb : d80446 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79325, d80446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d79325, d80446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d79326 q = 1) (hb : d80447 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d79326, d80447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79326, d80447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8526 (p : Pattern) (ha : d79332 p = 1) (hb : d80453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79327 q = 1) (hb : d80448 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d79327, d80448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79327, d80448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8525 q ha hb
  have h2 (q : Pattern) (ha : d79328 q = 1) (hb : d80449 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d79328, d80449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79328, d80449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79329 q = 1) (hb : d80450 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d79329, d80450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79329, d80450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79330 q = 1) (hb : d80451 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d79330, d80451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79330, d80451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79331 q = 1) (hb : d80452 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d79331, d80452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79331, d80452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79332 q = 1) (hb : d80453 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d79332, d80453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79332, d80453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8527 (p : Pattern) (ha : d79390 p = 1) (hb : d80104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79365 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79371 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79384 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79342 q = 1) (hb : d80099 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79342, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8419 q ha hb
    | true =>
      simp only [d79342, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79385 q = 1) (hb : d80100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79385, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d79385, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d79386 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d79387 q = 1) (hb : d80101 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79387, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79387, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d79388 q = 1) (hb : d80102 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79388, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d79388, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79389 q = 1) (hb : d80103 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79389, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79389, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79390 q = 1) (hb : d80104 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79390, d80104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79390, d80104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8528 (p : Pattern) (ha : d79408 p = 1) (hb : d80113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79365 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79371 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79384 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79342 q = 1) (hb : d80099 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79342, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8419 q ha hb
    | true =>
      simp only [d79342, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79385 q = 1) (hb : d80100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79385, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d79385, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d79386 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d79387 q = 1) (hb : d80101 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79387, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79387, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d79388 q = 1) (hb : d80102 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79388, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79388, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79389 q = 1) (hb : d80103 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79389, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79389, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d79395 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d79399 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d79402 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d79351 q = 1) (hb : d80108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79351, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8421 q ha hb
    | true =>
      simp only [d79351, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d79403 q = 1) (hb : d80109 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79403, d80109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d79403, d80109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d79404 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d79405 q = 1) (hb : d80110 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79405, d80110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d79405, d80110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d79406 q = 1) (hb : d80111 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79406, d80111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d79406, d80111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d79407 q = 1) (hb : d80112 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79407, d80112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d79407, d80112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d79408 q = 1) (hb : d80113 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79408, d80113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79408, d80113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8529 (p : Pattern) (ha : d79422 p = 1) (hb : d80459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79402 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79351 q = 1) (hb : d80108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79351, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8421 q ha hb
    | true =>
      simp only [d79351, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79403 q = 1) (hb : d80109 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79403, d80109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79403, d80109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d79404 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79405 q = 1) (hb : d80110 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79405, d80110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79405, d80110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79420 q = 1) (hb : d80111 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79420, d80111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79420, d80111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79421 q = 1) (hb : d80112 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79421, d80112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79421, d80112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79422 q = 1) (hb : d80459 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79422, d80459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79422, d80459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8530 (p : Pattern) (ha : d79453 p = 1) (hb : d80469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79440 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79447 q = 1) (hb : d80179 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79447, d80179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8436 q ha hb
    | true =>
      simp only [d79447, d80179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79448 q = 1) (hb : d80465 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79448, d80465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79448, d80465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d79449 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79450 q = 1) (hb : d80466 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79450, d80466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79450, d80466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79451 q = 1) (hb : d80467 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79451, d80467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79451, d80467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79452 q = 1) (hb : d80468 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79452, d80468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79452, d80468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79453 q = 1) (hb : d80469 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79453, d80469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79453, d80469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8531 (p : Pattern) (ha : d79459 p = 1) (hb : d80475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79409 q = 1) (hb : d80114 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79409, d80114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8527 q ha hb
    | true =>
      simp only [d79409, d80114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8528 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79416 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d79417 q = 1) (hb : d80115 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79417, d80115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79417, d80115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79418 q = 1) (hb : d80457 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79418, d80457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79418, d80457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79419 q = 1) (hb : d80458 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79419, d80458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79419, d80458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79423 q = 1) (hb : d80460 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79423, d80460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d79423, d80460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8529 q ha hb
  have h8 (q : Pattern) (ha : d79424 q = 1) (hb : d80461 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79424, d80461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79424, d80461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d79425 q = 1) (hb : d80462 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79425, d80462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d79425, d80462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d79426 q = 1) (hb : d80463 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79426, d80463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79426, d80463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d79427 q = 1) (hb : d80464 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79427, d80464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79427, d80464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d79454 q = 1) (hb : d80470 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79454, d80470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d79454, d80470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8530 q ha hb
  have h13 (q : Pattern) (ha : d79455 q = 1) (hb : d80471 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79455, d80471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79455, d80471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d79456 q = 1) (hb : d80472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79456, d80472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d79456, d80472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d79457 q = 1) (hb : d80473 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79457, d80473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d79457, d80473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d79458 q = 1) (hb : d80474 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79458, d80474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d79458, d80474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d79459 q = 1) (hb : d80475 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d79459, d80475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79459, d80475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8532 (p : Pattern) (ha : d79465 p = 1) (hb : d80481 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79460 q = 1) (hb : d80476 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d79460, d80476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79460, d80476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8531 q ha hb
  have h2 (q : Pattern) (ha : d79461 q = 1) (hb : d80477 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d79461, d80477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79461, d80477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79462 q = 1) (hb : d80478 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d79462, d80478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79462, d80478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79463 q = 1) (hb : d80479 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d79463, d80479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79463, d80479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79464 q = 1) (hb : d80480 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d79464, d80480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79464, d80480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79465 q = 1) (hb : d80481 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d79465, d80481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79465, d80481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8533 (p : Pattern) (ha : d79524 p = 1) (hb : d80210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79499 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79505 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79518 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79476 q = 1) (hb : d80205 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79476, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8441 q ha hb
    | true =>
      simp only [d79476, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79519 q = 1) (hb : d80206 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79519, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d79519, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d79520 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d79521 q = 1) (hb : d80207 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79521, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79521, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d79522 q = 1) (hb : d80208 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79522, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d79522, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79523 q = 1) (hb : d80209 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79523, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79523, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79524 q = 1) (hb : d80210 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79524, d80210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79524, d80210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8534 (p : Pattern) (ha : d79542 p = 1) (hb : d80219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79499 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79505 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79518 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79476 q = 1) (hb : d80205 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79476, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8441 q ha hb
    | true =>
      simp only [d79476, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79519 q = 1) (hb : d80206 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79519, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d79519, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d79520 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d79521 q = 1) (hb : d80207 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79521, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79521, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d79522 q = 1) (hb : d80208 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79522, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79522, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79523 q = 1) (hb : d80209 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79523, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79523, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d79529 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d79533 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d79536 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d79485 q = 1) (hb : d80214 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79485, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8443 q ha hb
    | true =>
      simp only [d79485, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d79537 q = 1) (hb : d80215 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79537, d80215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d79537, d80215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d79538 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d79539 q = 1) (hb : d80216 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79539, d80216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d79539, d80216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d79540 q = 1) (hb : d80217 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79540, d80217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d79540, d80217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d79541 q = 1) (hb : d80218 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79541, d80218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d79541, d80218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d79542 q = 1) (hb : d80219 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79542, d80219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79542, d80219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8535 (p : Pattern) (ha : d79556 p = 1) (hb : d80488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79536 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79485 q = 1) (hb : d80214 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79485, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8443 q ha hb
    | true =>
      simp only [d79485, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79537 q = 1) (hb : d80215 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79537, d80215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79537, d80215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d79538 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79539 q = 1) (hb : d80216 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79539, d80216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79539, d80216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79554 q = 1) (hb : d80217 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79554, d80217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79554, d80217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79555 q = 1) (hb : d80218 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79555, d80218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79555, d80218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79556 q = 1) (hb : d80488 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79556, d80488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79556, d80488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8536 (p : Pattern) (ha : d79587 p = 1) (hb : d80498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79574 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79581 q = 1) (hb : d80285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79581, d80285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8458 q ha hb
    | true =>
      simp only [d79581, d80285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79582 q = 1) (hb : d80494 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79582, d80494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79582, d80494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d79583 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79584 q = 1) (hb : d80495 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79584, d80495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79584, d80495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79585 q = 1) (hb : d80496 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79585, d80496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79585, d80496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79586 q = 1) (hb : d80497 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79586, d80497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79586, d80497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79587 q = 1) (hb : d80498 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79587, d80498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79587, d80498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8537 (p : Pattern) (ha : d79593 p = 1) (hb : d80504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79543 q = 1) (hb : d80220 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79543, d80220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8533 q ha hb
    | true =>
      simp only [d79543, d80220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8534 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79550 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d79551 q = 1) (hb : d80221 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79551, d80221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79551, d80221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79552 q = 1) (hb : d80486 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79552, d80486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79552, d80486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79553 q = 1) (hb : d80487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79553, d80487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79553, d80487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79557 q = 1) (hb : d80489 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79557, d80489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d79557, d80489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8535 q ha hb
  have h8 (q : Pattern) (ha : d79558 q = 1) (hb : d80490 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79558, d80490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79558, d80490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d79559 q = 1) (hb : d80491 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79559, d80491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d79559, d80491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d79560 q = 1) (hb : d80492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79560, d80492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79560, d80492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d79561 q = 1) (hb : d80493 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79561, d80493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79561, d80493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d79588 q = 1) (hb : d80499 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79588, d80499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d79588, d80499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8536 q ha hb
  have h13 (q : Pattern) (ha : d79589 q = 1) (hb : d80500 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79589, d80500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79589, d80500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d79590 q = 1) (hb : d80501 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79590, d80501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d79590, d80501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d79591 q = 1) (hb : d80502 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79591, d80502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d79591, d80502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d79592 q = 1) (hb : d80503 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79592, d80503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d79592, d80503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d79593 q = 1) (hb : d80504 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d79593, d80504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79593, d80504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8538 (p : Pattern) (ha : d79599 p = 1) (hb : d80510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79594 q = 1) (hb : d80505 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d79594, d80505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79594, d80505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8537 q ha hb
  have h2 (q : Pattern) (ha : d79595 q = 1) (hb : d80506 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d79595, d80506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79595, d80506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79596 q = 1) (hb : d80507 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d79596, d80507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79596, d80507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79597 q = 1) (hb : d80508 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d79597, d80508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79597, d80508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79598 q = 1) (hb : d80509 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d79598, d80509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79598, d80509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79599 q = 1) (hb : d80510 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d79599, d80510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79599, d80510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8539 (p : Pattern) (ha : d79605 p = 1) (hb : d80516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d79070 q = 1) (hb : d80401 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d79070, d80401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8508 q ha hb
    | true =>
      simp only [d79070, d80401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8514 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79201 q = 1) (hb : d80427 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d79201, d80427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79201, d80427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8520 q ha hb
  have h3 (q : Pattern) (ha : d79202 q = 1) (hb : d80428 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d79202, d80428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79202, d80428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79333 q = 1) (hb : d80454 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d79333, d80454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79333, d80454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8526 q ha hb
  have h5 (q : Pattern) (ha : d79334 q = 1) (hb : d80455 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d79334, d80455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79334, d80455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79335 q = 1) (hb : d80456 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d79335, d80456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79335, d80456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79466 q = 1) (hb : d80482 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d79466, d80482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79466, d80482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8532 q ha hb
  have h8 (q : Pattern) (ha : d79467 q = 1) (hb : d80483 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d79467, d80483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79467, d80483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79468 q = 1) (hb : d80484 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d79468, d80484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79468, d80484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79469 q = 1) (hb : d80485 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d79469, d80485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79469, d80485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d79600 q = 1) (hb : d80511 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d79600, d80511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79600, d80511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8538 q ha hb
  have h12 (q : Pattern) (ha : d79601 q = 1) (hb : d80512 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d79601, d80512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79601, d80512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d79602 q = 1) (hb : d80513 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d79602, d80513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79602, d80513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d79603 q = 1) (hb : d80514 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d79603, d80514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79603, d80514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d79604 q = 1) (hb : d80515 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d79604, d80515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d79604, d80515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79605 q = 1) (hb : d80516 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d79605, d80516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d79605, d80516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro8540 (p : Pattern) (ha : d79611 p = 1) (hb : d80522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79606 q = 1) (hb : d80517 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d79606, d80517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8539 q ha hb
    | true =>
      simp only [d79606, d80517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79607 q = 1) (hb : d80518 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d79607, d80518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79607, d80518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79608 q = 1) (hb : d80519 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d79608, d80519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79608, d80519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79609 q = 1) (hb : d80520 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d79609, d80520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79609, d80520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79610 q = 1) (hb : d80521 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d79610, d80521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79610, d80521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79611 q = 1) (hb : d80522 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d79611, d80522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79611, d80522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8541 (p : Pattern) (ha : d79617 p = 1) (hb : d80528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79612 q = 1) (hb : d80523 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d79612, d80523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8540 q ha hb
    | true =>
      simp only [d79612, d80523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79613 q = 1) (hb : d80524 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d79613, d80524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79613, d80524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79614 q = 1) (hb : d80525 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d79614, d80525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79614, d80525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79615 q = 1) (hb : d80526 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d79615, d80526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79615, d80526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79616 q = 1) (hb : d80527 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d79616, d80527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79616, d80527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79617 q = 1) (hb : d80528 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d79617, d80528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79617, d80528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8542 (p : Pattern) (ha : d79623 p = 1) (hb : d80534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79618 q = 1) (hb : d80529 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d79618, d80529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8541 q ha hb
    | true =>
      simp only [d79618, d80529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79619 q = 1) (hb : d80530 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d79619, d80530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79619, d80530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79620 q = 1) (hb : d80531 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d79620, d80531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79620, d80531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79621 q = 1) (hb : d80532 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d79621, d80532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79621, d80532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79622 q = 1) (hb : d80533 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d79622, d80533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79622, d80533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79623 q = 1) (hb : d80534 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d79623, d80534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79623, d80534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8543 (p : Pattern) (ha : d79629 p = 1) (hb : d80540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79624 q = 1) (hb : d80535 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d79624, d80535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8542 q ha hb
    | true =>
      simp only [d79624, d80535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79625 q = 1) (hb : d80536 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d79625, d80536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79625, d80536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79626 q = 1) (hb : d80537 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d79626, d80537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79626, d80537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79627 q = 1) (hb : d80538 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d79627, d80538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79627, d80538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79628 q = 1) (hb : d80539 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d79628, d80539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79628, d80539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79629 q = 1) (hb : d80540 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d79629, d80540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79629, d80540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8544 (p : Pattern) (ha : d79635 p = 1) (hb : d80546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79630 q = 1) (hb : d80541 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d79630, d80541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8543 q ha hb
    | true =>
      simp only [d79630, d80541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79631 q = 1) (hb : d80542 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d79631, d80542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79631, d80542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79632 q = 1) (hb : d80543 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d79632, d80543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79632, d80543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79633 q = 1) (hb : d80544 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d79633, d80544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79633, d80544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79634 q = 1) (hb : d80545 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d79634, d80545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79634, d80545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79635 q = 1) (hb : d80546 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d79635, d80546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79635, d80546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8545 (p : Pattern) (ha : d79641 p = 1) (hb : d80552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79636 q = 1) (hb : d80547 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d79636, d80547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8544 q ha hb
    | true =>
      simp only [d79636, d80547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79637 q = 1) (hb : d80548 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d79637, d80548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79637, d80548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79638 q = 1) (hb : d80549 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d79638, d80549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79638, d80549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79639 q = 1) (hb : d80550 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d79639, d80550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79639, d80550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79640 q = 1) (hb : d80551 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d79640, d80551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79640, d80551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79641 q = 1) (hb : d80552 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d79641, d80552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79641, d80552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8546 (p : Pattern) (ha : d79647 p = 1) (hb : d80558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79642 q = 1) (hb : d80553 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d79642, d80553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8545 q ha hb
    | true =>
      simp only [d79642, d80553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79643 q = 1) (hb : d80554 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d79643, d80554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79643, d80554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79644 q = 1) (hb : d80555 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d79644, d80555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79644, d80555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79645 q = 1) (hb : d80556 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d79645, d80556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79645, d80556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79646 q = 1) (hb : d80557 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d79646, d80557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79646, d80557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79647 q = 1) (hb : d80558 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d79647, d80558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79647, d80558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8547 (p : Pattern) (ha : d79700 p = 1) (hb : d80563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77918 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77924 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77931 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d79652 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79696 q = 1) (hb : d80559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79696, d80559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79696, d80559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d77853 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d79697 q = 1) (hb : d80560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79697, d80560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79697, d80560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79698 q = 1) (hb : d80561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79698, d80561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79698, d80561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79699 q = 1) (hb : d80562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79699, d80562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79699, d80562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79700 q = 1) (hb : d80563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79700, d80563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79700, d80563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8548 (p : Pattern) (ha : d79707 p = 1) (hb : d80568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77918 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77924 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77931 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79652 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79696 q = 1) (hb : d80559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79696, d80559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79696, d80559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d77853 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d79697 q = 1) (hb : d80560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79697, d80560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79697, d80560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79698 q = 1) (hb : d80561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79698, d80561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79698, d80561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79699 q = 1) (hb : d80562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79699, d80562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79699, d80562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d77948 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d77952 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d77954 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d79659 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d79703 q = 1) (hb : d80564 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79703, d80564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79703, d80564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d77860 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d79704 q = 1) (hb : d80565 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79704, d80565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d79704, d80565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79705 q = 1) (hb : d80566 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79705, d80566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d79705, d80566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d79706 q = 1) (hb : d80567 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79706, d80567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79706, d80567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d79707 q = 1) (hb : d80568 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79707, d80568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d79707, d80568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro8549 (p : Pattern) (ha : d80353 p = 1) (hb : d80575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77954 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79659 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d79703 q = 1) (hb : d80564 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79703, d80564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79703, d80564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d77860 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79704 q = 1) (hb : d80565 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79704, d80565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79704, d80565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79705 q = 1) (hb : d80573 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79705, d80573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79705, d80573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79706 q = 1) (hb : d80574 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79706, d80574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79706, d80574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80353 q = 1) (hb : d80575 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80353, d80575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80353, d80575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8550 (p : Pattern) (ha : d80363 p = 1) (hb : d80585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77982 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79679 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80359 q = 1) (hb : d80581 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80359, d80581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80359, d80581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d77882 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80360 q = 1) (hb : d80582 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80360, d80582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80360, d80582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80361 q = 1) (hb : d80583 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80361, d80583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80361, d80583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80362 q = 1) (hb : d80584 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80362, d80584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80362, d80584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80363 q = 1) (hb : d80585 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80363, d80585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80363, d80585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8551 (p : Pattern) (ha : d80369 p = 1) (hb : d80591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77912 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79708 q = 1) (hb : d80569 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79708, d80569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8547 q ha hb
    | true =>
      simp only [d79708, d80569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8548 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77964 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d79709 q = 1) (hb : d80570 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79709, d80570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79709, d80570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80351 q = 1) (hb : d80571 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80351, d80571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80351, d80571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80352 q = 1) (hb : d80572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80352, d80572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80352, d80572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80354 q = 1) (hb : d80576 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80354, d80576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80354, d80576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8549 q ha hb
  have h8 (q : Pattern) (ha : d80355 q = 1) (hb : d80577 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80355, d80577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d80355, d80577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d80356 q = 1) (hb : d80578 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80356, d80578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80356, d80578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d80357 q = 1) (hb : d80579 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80357, d80579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80357, d80579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d80358 q = 1) (hb : d80580 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80358, d80580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80358, d80580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d80364 q = 1) (hb : d80586 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80364, d80586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80364, d80586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8550 q ha hb
  have h13 (q : Pattern) (ha : d80365 q = 1) (hb : d80587 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80365, d80587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80365, d80587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d80366 q = 1) (hb : d80588 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80366, d80588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80366, d80588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d80367 q = 1) (hb : d80589 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80367, d80589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d80367, d80589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d80368 q = 1) (hb : d80590 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80368, d80590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80368, d80590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d80369 q = 1) (hb : d80591 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d80369, d80591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80369, d80591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8552 (p : Pattern) (ha : d80375 p = 1) (hb : d80597 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77897 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d80370 q = 1) (hb : d80592 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d80370, d80592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80370, d80592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8551 q ha hb
  have h3 (q : Pattern) (ha : d80371 q = 1) (hb : d80593 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d80371, d80593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80371, d80593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80372 q = 1) (hb : d80594 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d80372, d80594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80372, d80594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d80373 q = 1) (hb : d80595 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d80373, d80595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80373, d80595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80374 q = 1) (hb : d80596 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d80374, d80596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80374, d80596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80375 q = 1) (hb : d80597 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d80375, d80597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80375, d80597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8553 (p : Pattern) (ha : d79792 p = 1) (hb : d80602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78036 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78042 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78055 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d79787 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79788 q = 1) (hb : d80598 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79788, d80598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79788, d80598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d78064 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d79789 q = 1) (hb : d80599 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79789, d80599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79789, d80599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79790 q = 1) (hb : d80600 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79790, d80600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79790, d80600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79791 q = 1) (hb : d80601 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79791, d80601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79791, d80601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79792 q = 1) (hb : d80602 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79792, d80602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79792, d80602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8554 (p : Pattern) (ha : d79801 p = 1) (hb : d80607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78036 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78042 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78055 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79787 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79788 q = 1) (hb : d80598 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79788, d80598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79788, d80598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d78064 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d79789 q = 1) (hb : d80599 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79789, d80599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79789, d80599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79790 q = 1) (hb : d80600 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79790, d80600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79790, d80600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79791 q = 1) (hb : d80601 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79791, d80601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79791, d80601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d78073 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d78077 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d78080 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d79796 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d79797 q = 1) (hb : d80603 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79797, d80603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79797, d80603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d78084 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d79798 q = 1) (hb : d80604 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79798, d80604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d79798, d80604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79799 q = 1) (hb : d80605 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79799, d80605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d79799, d80605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d79800 q = 1) (hb : d80606 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79800, d80606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79800, d80606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d79801 q = 1) (hb : d80607 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79801, d80607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d79801, d80607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro8555 (p : Pattern) (ha : d80378 p = 1) (hb : d80614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78080 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79796 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d79797 q = 1) (hb : d80603 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79797, d80603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79797, d80603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d78084 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79798 q = 1) (hb : d80604 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79798, d80604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79798, d80604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79799 q = 1) (hb : d80612 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79799, d80612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79799, d80612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79800 q = 1) (hb : d80613 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79800, d80613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79800, d80613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80378 q = 1) (hb : d80614 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80378, d80614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80378, d80614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8556 (p : Pattern) (ha : d80388 p = 1) (hb : d80624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79867 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80384 q = 1) (hb : d80620 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80384, d80620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80384, d80620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d78136 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80385 q = 1) (hb : d80621 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80385, d80621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80385, d80621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80386 q = 1) (hb : d80622 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80386, d80622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80386, d80622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80387 q = 1) (hb : d80623 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80387, d80623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80387, d80623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80388 q = 1) (hb : d80624 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80388, d80624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80388, d80624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8557 (p : Pattern) (ha : d80394 p = 1) (hb : d80630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78030 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79802 q = 1) (hb : d80608 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79802, d80608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8553 q ha hb
    | true =>
      simp only [d79802, d80608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8554 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78096 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d79803 q = 1) (hb : d80609 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79803, d80609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79803, d80609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80376 q = 1) (hb : d80610 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80376, d80610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80376, d80610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80377 q = 1) (hb : d80611 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80377, d80611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80377, d80611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80379 q = 1) (hb : d80615 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80379, d80615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80379, d80615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8555 q ha hb
  have h8 (q : Pattern) (ha : d80380 q = 1) (hb : d80616 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80380, d80616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d80380, d80616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d80381 q = 1) (hb : d80617 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80381, d80617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80381, d80617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d80382 q = 1) (hb : d80618 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80382, d80618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80382, d80618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d80383 q = 1) (hb : d80619 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80383, d80619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80383, d80619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d80389 q = 1) (hb : d80625 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80389, d80625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80389, d80625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8556 q ha hb
  have h13 (q : Pattern) (ha : d80390 q = 1) (hb : d80626 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80390, d80626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80390, d80626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d80391 q = 1) (hb : d80627 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80391, d80627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80391, d80627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d80392 q = 1) (hb : d80628 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80392, d80628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d80392, d80628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d80393 q = 1) (hb : d80629 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80393, d80629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80393, d80629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d80394 q = 1) (hb : d80630 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d80394, d80630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80394, d80630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8558 (p : Pattern) (ha : d80400 p = 1) (hb : d80636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80395 q = 1) (hb : d80631 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d80395, d80631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80395, d80631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8557 q ha hb
  have h2 (q : Pattern) (ha : d80396 q = 1) (hb : d80632 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d80396, d80632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80396, d80632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80397 q = 1) (hb : d80633 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d80397, d80633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80397, d80633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80398 q = 1) (hb : d80634 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d80398, d80634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80398, d80634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d80399 q = 1) (hb : d80635 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d80399, d80635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80399, d80635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80400 q = 1) (hb : d80636 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d80400, d80636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80400, d80636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8559 (p : Pattern) (ha : d79895 p = 1) (hb : d80642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78183 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78189 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78202 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d79890 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79891 q = 1) (hb : d80638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79891, d80638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79891, d80638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d78211 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d79892 q = 1) (hb : d80639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79892, d80639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79892, d80639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79893 q = 1) (hb : d80640 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79893, d80640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79893, d80640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79894 q = 1) (hb : d80641 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79894, d80641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79894, d80641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79895 q = 1) (hb : d80642 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79895, d80642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79895, d80642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8560 (p : Pattern) (ha : d79904 p = 1) (hb : d80647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78183 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78189 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78202 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79891 q = 1) (hb : d80638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79891, d80638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79891, d80638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d78211 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d79892 q = 1) (hb : d80639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79892, d80639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79892, d80639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79893 q = 1) (hb : d80640 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79893, d80640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79893, d80640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79894 q = 1) (hb : d80641 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79894, d80641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79894, d80641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d78220 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d78224 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d78227 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d79899 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d79900 q = 1) (hb : d80643 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79900, d80643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79900, d80643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d78231 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d79901 q = 1) (hb : d80644 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79901, d80644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d79901, d80644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79902 q = 1) (hb : d80645 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79902, d80645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d79902, d80645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d79903 q = 1) (hb : d80646 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79903, d80646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79903, d80646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d79904 q = 1) (hb : d80647 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79904, d80647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d79904, d80647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro8561 (p : Pattern) (ha : d80404 p = 1) (hb : d80654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78227 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79899 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d79900 q = 1) (hb : d80643 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79900, d80643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79900, d80643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d78231 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79901 q = 1) (hb : d80644 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79901, d80644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79901, d80644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79902 q = 1) (hb : d80652 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79902, d80652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79902, d80652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79903 q = 1) (hb : d80653 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79903, d80653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79903, d80653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80404 q = 1) (hb : d80654 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80404, d80654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80404, d80654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8562 (p : Pattern) (ha : d80414 p = 1) (hb : d80664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78267 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79970 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80410 q = 1) (hb : d80660 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80410, d80660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80410, d80660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d78283 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80411 q = 1) (hb : d80661 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80411, d80661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80411, d80661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80412 q = 1) (hb : d80662 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80412, d80662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80412, d80662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80413 q = 1) (hb : d80663 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80413, d80663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80413, d80663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80414 q = 1) (hb : d80664 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80414, d80664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80414, d80664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8563 (p : Pattern) (ha : d80420 p = 1) (hb : d80670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78177 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79905 q = 1) (hb : d80648 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79905, d80648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8559 q ha hb
    | true =>
      simp only [d79905, d80648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8560 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78243 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d79906 q = 1) (hb : d80649 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79906, d80649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79906, d80649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80402 q = 1) (hb : d80650 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80402, d80650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80402, d80650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80403 q = 1) (hb : d80651 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80403, d80651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80403, d80651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80405 q = 1) (hb : d80655 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80405, d80655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80405, d80655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8561 q ha hb
  have h8 (q : Pattern) (ha : d80406 q = 1) (hb : d80656 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80406, d80656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d80406, d80656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d80407 q = 1) (hb : d80657 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80407, d80657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80407, d80657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d80408 q = 1) (hb : d80658 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80408, d80658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80408, d80658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d80409 q = 1) (hb : d80659 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80409, d80659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80409, d80659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d80415 q = 1) (hb : d80665 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80415, d80665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80415, d80665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8562 q ha hb
  have h13 (q : Pattern) (ha : d80416 q = 1) (hb : d80666 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80416, d80666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80416, d80666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d80417 q = 1) (hb : d80667 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80417, d80667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80417, d80667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d80418 q = 1) (hb : d80668 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80418, d80668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d80418, d80668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d80419 q = 1) (hb : d80669 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80419, d80669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80419, d80669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d80420 q = 1) (hb : d80670 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d80420, d80670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80420, d80670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8564 (p : Pattern) (ha : d80426 p = 1) (hb : d80676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80421 q = 1) (hb : d80671 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d80421, d80671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80421, d80671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8563 q ha hb
  have h2 (q : Pattern) (ha : d80422 q = 1) (hb : d80672 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d80422, d80672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80422, d80672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80423 q = 1) (hb : d80673 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d80423, d80673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80423, d80673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80424 q = 1) (hb : d80674 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d80424, d80674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80424, d80674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d80425 q = 1) (hb : d80675 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d80425, d80675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80425, d80675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80426 q = 1) (hb : d80676 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d80426, d80676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80426, d80676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8565 (p : Pattern) (ha : d79999 p = 1) (hb : d80683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78331 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78337 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78350 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d79994 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79995 q = 1) (hb : d80679 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79995, d80679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79995, d80679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d78359 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d79996 q = 1) (hb : d80680 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79996, d80680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79996, d80680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79997 q = 1) (hb : d80681 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79997, d80681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79997, d80681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79998 q = 1) (hb : d80682 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79998, d80682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79998, d80682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79999 q = 1) (hb : d80683 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79999, d80683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79999, d80683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8566 (p : Pattern) (ha : d80008 p = 1) (hb : d80688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78331 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78337 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78350 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79994 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79995 q = 1) (hb : d80679 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79995, d80679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79995, d80679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d78359 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d79996 q = 1) (hb : d80680 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79996, d80680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79996, d80680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79997 q = 1) (hb : d80681 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79997, d80681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79997, d80681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79998 q = 1) (hb : d80682 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79998, d80682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79998, d80682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d78368 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d78372 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d78375 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d80003 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d80004 q = 1) (hb : d80684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80004, d80684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80004, d80684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d78379 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d80005 q = 1) (hb : d80685 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80005, d80685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80005, d80685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d80006 q = 1) (hb : d80686 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80006, d80686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d80006, d80686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d80007 q = 1) (hb : d80687 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80007, d80687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80007, d80687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d80008 q = 1) (hb : d80688 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80008, d80688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80008, d80688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro8567 (p : Pattern) (ha : d80431 p = 1) (hb : d80695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78375 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d80003 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80004 q = 1) (hb : d80684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80004, d80684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80004, d80684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d78379 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80005 q = 1) (hb : d80685 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80005, d80685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80005, d80685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80006 q = 1) (hb : d80693 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80006, d80693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80006, d80693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80007 q = 1) (hb : d80694 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80007, d80694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80007, d80694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80431 q = 1) (hb : d80695 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80431, d80695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80431, d80695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8568 (p : Pattern) (ha : d80441 p = 1) (hb : d80705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78415 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d80074 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80437 q = 1) (hb : d80701 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80437, d80701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80437, d80701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d78431 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80438 q = 1) (hb : d80702 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80438, d80702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80438, d80702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80439 q = 1) (hb : d80703 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80439, d80703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80439, d80703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80440 q = 1) (hb : d80704 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80440, d80704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80440, d80704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80441 q = 1) (hb : d80705 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80441, d80705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80441, d80705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8569 (p : Pattern) (ha : d80447 p = 1) (hb : d80711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78325 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80009 q = 1) (hb : d80689 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80009, d80689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8565 q ha hb
    | true =>
      simp only [d80009, d80689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8566 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78391 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80010 q = 1) (hb : d80690 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80010, d80690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80010, d80690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80429 q = 1) (hb : d80691 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80429, d80691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80429, d80691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80430 q = 1) (hb : d80692 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80430, d80692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80430, d80692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80432 q = 1) (hb : d80696 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80432, d80696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80432, d80696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8567 q ha hb
  have h8 (q : Pattern) (ha : d80433 q = 1) (hb : d80697 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80433, d80697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d80433, d80697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d80434 q = 1) (hb : d80698 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80434, d80698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80434, d80698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d80435 q = 1) (hb : d80699 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80435, d80699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80435, d80699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d80436 q = 1) (hb : d80700 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80436, d80700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80436, d80700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d80442 q = 1) (hb : d80706 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80442, d80706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80442, d80706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8568 q ha hb
  have h13 (q : Pattern) (ha : d80443 q = 1) (hb : d80707 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80443, d80707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80443, d80707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d80444 q = 1) (hb : d80708 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80444, d80708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80444, d80708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d80445 q = 1) (hb : d80709 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80445, d80709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d80445, d80709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d80446 q = 1) (hb : d80710 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80446, d80710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80446, d80710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d80447 q = 1) (hb : d80711 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d80447, d80711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80447, d80711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8570 (p : Pattern) (ha : d80453 p = 1) (hb : d80717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80448 q = 1) (hb : d80712 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d80448, d80712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80448, d80712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8569 q ha hb
  have h2 (q : Pattern) (ha : d80449 q = 1) (hb : d80713 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d80449, d80713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80449, d80713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80450 q = 1) (hb : d80714 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d80450, d80714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80450, d80714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80451 q = 1) (hb : d80715 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d80451, d80715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80451, d80715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d80452 q = 1) (hb : d80716 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d80452, d80716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80452, d80716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80453 q = 1) (hb : d80717 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d80453, d80717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80453, d80717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8571 (p : Pattern) (ha : d80104 p = 1) (hb : d80725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78480 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78486 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78499 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d80099 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80100 q = 1) (hb : d80721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80100, d80721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80100, d80721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d78508 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d80101 q = 1) (hb : d80722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80101, d80722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80101, d80722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80102 q = 1) (hb : d80723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80102, d80723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80102, d80723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d80103 q = 1) (hb : d80724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80103, d80724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80103, d80724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d80104 q = 1) (hb : d80725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80104, d80725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80104, d80725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8572 (p : Pattern) (ha : d80113 p = 1) (hb : d80730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78480 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78486 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78499 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d80099 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d80100 q = 1) (hb : d80721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80100, d80721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80100, d80721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d78508 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d80101 q = 1) (hb : d80722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80101, d80722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80101, d80722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80102 q = 1) (hb : d80723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80102, d80723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80102, d80723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80103 q = 1) (hb : d80724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80103, d80724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80103, d80724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d78517 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d78521 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d78524 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d80108 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d80109 q = 1) (hb : d80726 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80109, d80726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80109, d80726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d78528 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d80110 q = 1) (hb : d80727 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80110, d80727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80110, d80727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d80111 q = 1) (hb : d80728 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80111, d80728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d80111, d80728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d80112 q = 1) (hb : d80729 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80112, d80729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80112, d80729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d80113 q = 1) (hb : d80730 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80113, d80730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80113, d80730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro8573 (p : Pattern) (ha : d80459 p = 1) (hb : d80737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78524 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d80108 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80109 q = 1) (hb : d80726 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80109, d80726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80109, d80726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d78528 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80110 q = 1) (hb : d80727 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80110, d80727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80110, d80727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80111 q = 1) (hb : d80735 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80111, d80735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80111, d80735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80112 q = 1) (hb : d80736 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80112, d80736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80112, d80736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80459 q = 1) (hb : d80737 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80459, d80737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80459, d80737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8574 (p : Pattern) (ha : d80469 p = 1) (hb : d80747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78564 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d80179 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80465 q = 1) (hb : d80743 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80465, d80743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80465, d80743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d78580 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80466 q = 1) (hb : d80744 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80466, d80744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80466, d80744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80467 q = 1) (hb : d80745 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80467, d80745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80467, d80745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80468 q = 1) (hb : d80746 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80468, d80746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80468, d80746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80469 q = 1) (hb : d80747 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80469, d80747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80469, d80747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8575 (p : Pattern) (ha : d80475 p = 1) (hb : d80753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78474 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80114 q = 1) (hb : d80731 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80114, d80731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8571 q ha hb
    | true =>
      simp only [d80114, d80731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8572 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78540 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80115 q = 1) (hb : d80732 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80115, d80732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80115, d80732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80457 q = 1) (hb : d80733 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80457, d80733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80457, d80733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80458 q = 1) (hb : d80734 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80458, d80734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80458, d80734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80460 q = 1) (hb : d80738 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80460, d80738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80460, d80738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8573 q ha hb
  have h8 (q : Pattern) (ha : d80461 q = 1) (hb : d80739 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80461, d80739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d80461, d80739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d80462 q = 1) (hb : d80740 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80462, d80740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80462, d80740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d80463 q = 1) (hb : d80741 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80463, d80741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80463, d80741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d80464 q = 1) (hb : d80742 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80464, d80742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80464, d80742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d80470 q = 1) (hb : d80748 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80470, d80748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80470, d80748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8574 q ha hb
  have h13 (q : Pattern) (ha : d80471 q = 1) (hb : d80749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80471, d80749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80471, d80749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d80472 q = 1) (hb : d80750 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80472, d80750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80472, d80750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d80473 q = 1) (hb : d80751 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80473, d80751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d80473, d80751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d80474 q = 1) (hb : d80752 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80474, d80752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80474, d80752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d80475 q = 1) (hb : d80753 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d80475, d80753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80475, d80753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8576 (p : Pattern) (ha : d80481 p = 1) (hb : d80759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80476 q = 1) (hb : d80754 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d80476, d80754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80476, d80754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8575 q ha hb
  have h2 (q : Pattern) (ha : d80477 q = 1) (hb : d80755 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d80477, d80755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80477, d80755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80478 q = 1) (hb : d80756 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d80478, d80756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80478, d80756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80479 q = 1) (hb : d80757 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d80479, d80757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80479, d80757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d80480 q = 1) (hb : d80758 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d80480, d80758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80480, d80758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80481 q = 1) (hb : d80759 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d80481, d80759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80481, d80759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8577 (p : Pattern) (ha : d80210 p = 1) (hb : d80768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78630 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78636 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78649 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d80205 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80206 q = 1) (hb : d80764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80206, d80764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80206, d80764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d78658 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d80207 q = 1) (hb : d80765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80207, d80765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80207, d80765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80208 q = 1) (hb : d80766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80208, d80766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80208, d80766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d80209 q = 1) (hb : d80767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80209, d80767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80209, d80767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d80210 q = 1) (hb : d80768 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80210, d80768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80210, d80768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8578 (p : Pattern) (ha : d80219 p = 1) (hb : d80773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78636 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78649 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d80205 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d80206 q = 1) (hb : d80764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80206, d80764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80206, d80764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d78658 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d80207 q = 1) (hb : d80765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80207, d80765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80207, d80765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80208 q = 1) (hb : d80766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80208, d80766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80208, d80766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80209 q = 1) (hb : d80767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80209, d80767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80209, d80767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d78667 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d78671 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d78674 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d80214 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d80215 q = 1) (hb : d80769 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80215, d80769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80215, d80769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d78678 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d80216 q = 1) (hb : d80770 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80216, d80770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80216, d80770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d80217 q = 1) (hb : d80771 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80217, d80771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d80217, d80771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d80218 q = 1) (hb : d80772 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80218, d80772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80218, d80772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d80219 q = 1) (hb : d80773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80219, d80773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80219, d80773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro8579 (p : Pattern) (ha : d80488 p = 1) (hb : d80780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78674 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d80214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80215 q = 1) (hb : d80769 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80215, d80769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80215, d80769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d78678 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80216 q = 1) (hb : d80770 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80216, d80770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80216, d80770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80217 q = 1) (hb : d80778 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80217, d80778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80217, d80778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80218 q = 1) (hb : d80779 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80218, d80779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80218, d80779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80488 q = 1) (hb : d80780 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80488, d80780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80488, d80780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8580 (p : Pattern) (ha : d80498 p = 1) (hb : d80790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78714 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d80285 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80494 q = 1) (hb : d80786 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80494, d80786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80494, d80786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d78730 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80495 q = 1) (hb : d80787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80495, d80787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80495, d80787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80496 q = 1) (hb : d80788 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80496, d80788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80496, d80788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80497 q = 1) (hb : d80789 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80497, d80789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80497, d80789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80498 q = 1) (hb : d80790 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80498, d80790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80498, d80790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8581 (p : Pattern) (ha : d80504 p = 1) (hb : d80796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78624 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80220 q = 1) (hb : d80774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80220, d80774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8577 q ha hb
    | true =>
      simp only [d80220, d80774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8578 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78690 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80221 q = 1) (hb : d80775 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80221, d80775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80221, d80775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80486 q = 1) (hb : d80776 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80486, d80776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80486, d80776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80487 q = 1) (hb : d80777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80487, d80777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80487, d80777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80489 q = 1) (hb : d80781 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80489, d80781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80489, d80781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8579 q ha hb
  have h8 (q : Pattern) (ha : d80490 q = 1) (hb : d80782 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80490, d80782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d80490, d80782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d80491 q = 1) (hb : d80783 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80491, d80783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80491, d80783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d80492 q = 1) (hb : d80784 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80492, d80784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80492, d80784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d80493 q = 1) (hb : d80785 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80493, d80785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80493, d80785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d80499 q = 1) (hb : d80791 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80499, d80791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80499, d80791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8580 q ha hb
  have h13 (q : Pattern) (ha : d80500 q = 1) (hb : d80792 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80500, d80792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80500, d80792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d80501 q = 1) (hb : d80793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80501, d80793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80501, d80793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d80502 q = 1) (hb : d80794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80502, d80794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d80502, d80794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d80503 q = 1) (hb : d80795 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80503, d80795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80503, d80795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d80504 q = 1) (hb : d80796 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d80504, d80796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80504, d80796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8582 (p : Pattern) (ha : d80510 p = 1) (hb : d80802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80505 q = 1) (hb : d80797 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d80505, d80797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80505, d80797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8581 q ha hb
  have h2 (q : Pattern) (ha : d80506 q = 1) (hb : d80798 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d80506, d80798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80506, d80798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80507 q = 1) (hb : d80799 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d80507, d80799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80507, d80799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80508 q = 1) (hb : d80800 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d80508, d80800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80508, d80800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d80509 q = 1) (hb : d80801 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d80509, d80801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80509, d80801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80510 q = 1) (hb : d80802 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d80510, d80802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80510, d80802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8583 (p : Pattern) (ha : d80516 p = 1) (hb : d80808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d80401 q = 1) (hb : d80637 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d80401, d80637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8552 q ha hb
    | true =>
      simp only [d80401, d80637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8558 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d80427 q = 1) (hb : d80677 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d80427, d80677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80427, d80677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8564 q ha hb
  have h3 (q : Pattern) (ha : d80428 q = 1) (hb : d80678 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d80428, d80678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80428, d80678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80454 q = 1) (hb : d80718 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d80454, d80718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80454, d80718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8570 q ha hb
  have h5 (q : Pattern) (ha : d80455 q = 1) (hb : d80719 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d80455, d80719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80455, d80719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80456 q = 1) (hb : d80720 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d80456, d80720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80456, d80720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80482 q = 1) (hb : d80760 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d80482, d80760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80482, d80760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8576 q ha hb
  have h8 (q : Pattern) (ha : d80483 q = 1) (hb : d80761 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d80483, d80761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80483, d80761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d80484 q = 1) (hb : d80762 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d80484, d80762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80484, d80762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d80485 q = 1) (hb : d80763 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d80485, d80763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80485, d80763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d80511 q = 1) (hb : d80803 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d80511, d80803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80511, d80803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8582 q ha hb
  have h12 (q : Pattern) (ha : d80512 q = 1) (hb : d80804 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d80512, d80804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80512, d80804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d80513 q = 1) (hb : d80805 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d80513, d80805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80513, d80805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d80514 q = 1) (hb : d80806 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d80514, d80806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80514, d80806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d80515 q = 1) (hb : d80807 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d80515, d80807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d80515, d80807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d80516 q = 1) (hb : d80808 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d80516, d80808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80516, d80808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro8584 (p : Pattern) (ha : d80522 p = 1) (hb : d80814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80517 q = 1) (hb : d80809 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d80517, d80809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8583 q ha hb
    | true =>
      simp only [d80517, d80809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80518 q = 1) (hb : d80810 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d80518, d80810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80518, d80810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80519 q = 1) (hb : d80811 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d80519, d80811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80519, d80811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80520 q = 1) (hb : d80812 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d80520, d80812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80520, d80812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80521 q = 1) (hb : d80813 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d80521, d80813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80521, d80813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80522 q = 1) (hb : d80814 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d80522, d80814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80522, d80814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8585 (p : Pattern) (ha : d80528 p = 1) (hb : d80820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80523 q = 1) (hb : d80815 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d80523, d80815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8584 q ha hb
    | true =>
      simp only [d80523, d80815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80524 q = 1) (hb : d80816 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d80524, d80816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80524, d80816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80525 q = 1) (hb : d80817 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d80525, d80817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80525, d80817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80526 q = 1) (hb : d80818 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d80526, d80818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80526, d80818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80527 q = 1) (hb : d80819 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d80527, d80819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80527, d80819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80528 q = 1) (hb : d80820 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d80528, d80820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80528, d80820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8586 (p : Pattern) (ha : d80534 p = 1) (hb : d80826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80529 q = 1) (hb : d80821 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d80529, d80821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8585 q ha hb
    | true =>
      simp only [d80529, d80821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80530 q = 1) (hb : d80822 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d80530, d80822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80530, d80822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80531 q = 1) (hb : d80823 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d80531, d80823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80531, d80823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80532 q = 1) (hb : d80824 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d80532, d80824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80532, d80824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80533 q = 1) (hb : d80825 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d80533, d80825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80533, d80825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80534 q = 1) (hb : d80826 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d80534, d80826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80534, d80826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8587 (p : Pattern) (ha : d80540 p = 1) (hb : d80832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80535 q = 1) (hb : d80827 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d80535, d80827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8586 q ha hb
    | true =>
      simp only [d80535, d80827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80536 q = 1) (hb : d80828 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d80536, d80828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80536, d80828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80537 q = 1) (hb : d80829 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d80537, d80829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80537, d80829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80538 q = 1) (hb : d80830 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d80538, d80830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80538, d80830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80539 q = 1) (hb : d80831 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d80539, d80831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80539, d80831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80540 q = 1) (hb : d80832 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d80540, d80832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80540, d80832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8588 (p : Pattern) (ha : d80546 p = 1) (hb : d80838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80541 q = 1) (hb : d80833 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d80541, d80833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8587 q ha hb
    | true =>
      simp only [d80541, d80833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80542 q = 1) (hb : d80834 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d80542, d80834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80542, d80834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80543 q = 1) (hb : d80835 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d80543, d80835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80543, d80835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80544 q = 1) (hb : d80836 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d80544, d80836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80544, d80836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80545 q = 1) (hb : d80837 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d80545, d80837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80545, d80837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80546 q = 1) (hb : d80838 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d80546, d80838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80546, d80838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8589 (p : Pattern) (ha : d80552 p = 1) (hb : d80844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80547 q = 1) (hb : d80839 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d80547, d80839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8588 q ha hb
    | true =>
      simp only [d80547, d80839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80548 q = 1) (hb : d80840 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d80548, d80840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80548, d80840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80549 q = 1) (hb : d80841 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d80549, d80841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80549, d80841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80550 q = 1) (hb : d80842 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d80550, d80842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80550, d80842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80551 q = 1) (hb : d80843 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d80551, d80843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80551, d80843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80552 q = 1) (hb : d80844 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d80552, d80844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80552, d80844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8590 (p : Pattern) (ha : d80558 p = 1) (hb : d80850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80553 q = 1) (hb : d80845 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d80553, d80845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8589 q ha hb
    | true =>
      simp only [d80553, d80845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80554 q = 1) (hb : d80846 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d80554, d80846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80554, d80846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80555 q = 1) (hb : d80847 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d80555, d80847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80555, d80847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80556 q = 1) (hb : d80848 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d80556, d80848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80556, d80848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80557 q = 1) (hb : d80849 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d80557, d80849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80557, d80849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80558 q = 1) (hb : d80850 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d80558, d80850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80558, d80850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8591 (p : Pattern) (ha : d213 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d103 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d213 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro8592 (p : Pattern) (ha : d69436 p = 1) (hb : d73190 p = 1) : d73194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d117 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d118 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d119 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d124 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d125 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d126 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69433 q = 1) (hb : d73190 q = 1) : d69433 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d69434 q = 1) (hb : d73190 q = 1) : d73192 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69434, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69434, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69435 q = 1) (hb : d73190 q = 1) : d73193 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69435, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69435, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69436 q = 1) (hb : d73190 q = 1) : d73194 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69436, d73194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69436, d73194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8593 (p : Pattern) (ha : d69440 p = 1) (hb : d73190 p = 1) : d73195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d117 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d118 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d119 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d124 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d125 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d126 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69433 q = 1) (hb : d73190 q = 1) : d69433 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d69434 q = 1) (hb : d73190 q = 1) : d73192 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69434, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69434, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69435 q = 1) (hb : d73190 q = 1) : d73193 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69435, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69435, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d195 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d196 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d197 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d198 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d200 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d201 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d202 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d69437 q = 1) (hb : d73190 q = 1) : d69437 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d69438 q = 1) (hb : d73190 q = 1) : d69445 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69438, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d69438, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d69439 q = 1) (hb : d73190 q = 1) : d69446 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69439, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69439, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d69440 q = 1) (hb : d73190 q = 1) : d73195 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69440, d73195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69440, d73195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro8594 (p : Pattern) (ha : d69972 p = 1) (hb : d73190 p = 1) : d73201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5069 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5069 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5070 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69441 q = 1) (hb : d73190 q = 1) : d73196 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69441, d73196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8592 q ha hb
    | true =>
      simp only [d69441, d73196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8593 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8591 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69968 q = 1) (hb : d73190 q = 1) : d73197 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69968, d73197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69968, d73197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69969 q = 1) (hb : d73190 q = 1) : d73198 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69969, d73198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69969, d73198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d69970 q = 1) (hb : d73190 q = 1) : d73199 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69970, d73199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69970, d73199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69451 q = 1) (hb : d73190 q = 1) : d69451 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d69971 q = 1) (hb : d73190 q = 1) : d73200 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69971, d73200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69971, d73200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69461 q = 1) (hb : d73190 q = 1) : d69461 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d69972 q = 1) (hb : d73190 q = 1) : d73201 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69972, d73201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69972, d73201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro8595 (p : Pattern) (ha : d4693 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d370 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4689 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4689, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4689, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4690 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4691 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4692 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4693 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8596 (p : Pattern) (ha : d4700 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d370 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4689 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4689, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4689, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4690 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4691 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4692 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d390 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4696 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4696, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4696, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d4697 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4698 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4699 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4700 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8597 (p : Pattern) (ha : d4742 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d4737 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4738 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4738, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4738, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4739 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4740 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4741 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d100 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d101 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d102 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d103 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4742 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8598 (p : Pattern) (ha : d69472 p = 1) (hb : d73190 p = 1) : d73209 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d4704 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4705 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4705, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4705, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4706 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4707 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d4708 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4709 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4709, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4709, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d4710 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69469 q = 1) (hb : d73190 q = 1) : d69469 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d69470 q = 1) (hb : d73190 q = 1) : d73207 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69470, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69470, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69471 q = 1) (hb : d73190 q = 1) : d73208 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69471, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69471, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69472 q = 1) (hb : d73190 q = 1) : d73209 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69472, d73209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69472, d73209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8599 (p : Pattern) (ha : d69477 p = 1) (hb : d73190 p = 1) : d73210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d4704 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4705 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4705, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4705, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4706 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4707 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d4708 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4709 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4709, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4709, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d4710 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69469 q = 1) (hb : d73190 q = 1) : d69469 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d69470 q = 1) (hb : d73190 q = 1) : d73207 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69470, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69470, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69471 q = 1) (hb : d73190 q = 1) : d73208 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69471, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69471, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d4718 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4719 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4719, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4719, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d4720 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4721 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d4722 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d4723 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4723, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4723, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d4724 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d69474 q = 1) (hb : d73190 q = 1) : d69474 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d69475 q = 1) (hb : d73190 q = 1) : d69482 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69475, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d69475, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d69476 q = 1) (hb : d73190 q = 1) : d69483 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69476, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69476, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d69477 q = 1) (hb : d73190 q = 1) : d73210 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69477, d73210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69477, d73210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro8600 (p : Pattern) (ha : d69989 p = 1) (hb : d73190 p = 1) : d73216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4694 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8595 q ha hb
  have h2 (q : Pattern) (ha : d4695 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4701 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8595 q ha hb
    | true =>
      simp only [d4701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8596 q ha hb
  have h4 (q : Pattern) (ha : d4702 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4703 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69478 q = 1) (hb : d73190 q = 1) : d73211 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69478, d73211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8598 q ha hb
    | true =>
      simp only [d69478, d73211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8599 q ha hb
  have h7 (q : Pattern) (ha : d4743 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8597 q ha hb
    | true =>
      simp only [d4743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5070 q ha hb
  have h8 (q : Pattern) (ha : d69978 q = 1) (hb : d73190 q = 1) : d73212 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69978, d73212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69978, d73212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69979 q = 1) (hb : d73190 q = 1) : d73213 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69979, d73213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69979, d73213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d69980 q = 1) (hb : d73190 q = 1) : d73214 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69980, d73214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69980, d73214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69485 q = 1) (hb : d73190 q = 1) : d69485 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5181 q ha hb
  have h13 (q : Pattern) (ha : d69981 q = 1) (hb : d73190 q = 1) : d69486 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69981, d69486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69981, d69486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69982 q = 1) (hb : d73190 q = 1) : d69487 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69982, d69487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69982, d69487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69983 q = 1) (hb : d73190 q = 1) : d69488 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69983, d69488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d69983, d69488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d69984 q = 1) (hb : d73190 q = 1) : d73215 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69984, d73215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69984, d73215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69495 q = 1) (hb : d73190 q = 1) : d69495 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5182 q ha hb
  have h19 (q : Pattern) (ha : d69985 q = 1) (hb : d73190 q = 1) : d69496 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69985, d69496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d69985, d69496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d69986 q = 1) (hb : d73190 q = 1) : d69497 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69986, d69497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d69986, d69497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d69987 q = 1) (hb : d73190 q = 1) : d69498 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69987, d69498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d69987, d69498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d69988 q = 1) (hb : d73190 q = 1) : d69499 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69988, d69499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d69988, d69499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d69989 q = 1) (hb : d73190 q = 1) : d73216 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69989, d73216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d69989, d73216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro8601 (p : Pattern) (ha : d69995 p = 1) (hb : d73190 p = 1) : d73222 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d73190 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69973 q = 1) (hb : d73190 q = 1) : d73202 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69973, d73202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69973, d73202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8594 q ha hb
  have h3 (q : Pattern) (ha : d69974 q = 1) (hb : d73190 q = 1) : d73203 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69974, d73203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69974, d73203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69975 q = 1) (hb : d73190 q = 1) : d73204 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69975, d73204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69975, d73204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69976 q = 1) (hb : d73190 q = 1) : d73205 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69976, d73205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69976, d73205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69977 q = 1) (hb : d73190 q = 1) : d73206 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69977, d73206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69977, d73206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69990 q = 1) (hb : d73190 q = 1) : d73217 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69990, d73217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69990, d73217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8600 q ha hb
  have h8 (q : Pattern) (ha : d69991 q = 1) (hb : d73190 q = 1) : d73218 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69991, d73218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69991, d73218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69992 q = 1) (hb : d73190 q = 1) : d73219 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69992, d73219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69992, d73219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69993 q = 1) (hb : d73190 q = 1) : d73220 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69993, d73220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69993, d73220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69994 q = 1) (hb : d73190 q = 1) : d73221 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69994, d73221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69994, d73221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69995 q = 1) (hb : d73190 q = 1) : d73222 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69995, d73222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69995, d73222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8602 (p : Pattern) (ha : d644 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d633 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d634 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d634, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d635 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d636 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d637 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d639 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d640 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d640, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d641 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d642 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d643 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d644 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8603 (p : Pattern) (ha : d653 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d639 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d640 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d640, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d641 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d642 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d643 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d653 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8604 (p : Pattern) (ha : d736 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d731 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d732 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d732, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d733 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d734 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d735 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d736 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8605 (p : Pattern) (ha : d4778 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d603 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4774 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4774, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4774, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4775 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4776 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4777 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4778 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8606 (p : Pattern) (ha : d4785 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d603 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4774 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4774, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4774, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4775 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4776 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4777 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d626 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4781 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4781, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4781, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d4782 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4783 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4784 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4785 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8607 (p : Pattern) (ha : d4836 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d4831 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4832 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4832, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4832, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4833 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4834 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4835 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d633 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d634 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d634, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d635 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d636 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d637 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4836 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8608 (p : Pattern) (ha : d69511 p = 1) (hb : d73190 p = 1) : d73225 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d4789 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4790 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4790, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4790, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4791 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4792 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d4793 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4794 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4794, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4794, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d4795 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69508 q = 1) (hb : d73190 q = 1) : d69508 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d69509 q = 1) (hb : d73190 q = 1) : d73223 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69509, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69509, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69510 q = 1) (hb : d73190 q = 1) : d73224 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69510, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69510, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69511 q = 1) (hb : d73190 q = 1) : d73225 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69511, d73225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69511, d73225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8609 (p : Pattern) (ha : d69516 p = 1) (hb : d73190 p = 1) : d73226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d4789 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4790 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4790, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4790, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4791 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4792 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d4793 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4794 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4794, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4794, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d4795 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69508 q = 1) (hb : d73190 q = 1) : d69508 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d69509 q = 1) (hb : d73190 q = 1) : d73223 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69509, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69509, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69510 q = 1) (hb : d73190 q = 1) : d73224 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69510, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69510, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d4803 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4804 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4804, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4804, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d4805 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4806 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d4807 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d4808 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4808, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4808, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d4809 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d69513 q = 1) (hb : d73190 q = 1) : d69513 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d69514 q = 1) (hb : d73190 q = 1) : d69521 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69514, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d69514, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d69515 q = 1) (hb : d73190 q = 1) : d69522 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69515, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69515, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d69516 q = 1) (hb : d73190 q = 1) : d73226 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69516, d73226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69516, d73226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro8610 (p : Pattern) (ha : d70007 p = 1) (hb : d73190 p = 1) : d73232 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4779 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8605 q ha hb
  have h2 (q : Pattern) (ha : d4780 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4786 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8605 q ha hb
    | true =>
      simp only [d4786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8606 q ha hb
  have h4 (q : Pattern) (ha : d4787 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4788 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69517 q = 1) (hb : d73190 q = 1) : d73227 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69517, d73227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8608 q ha hb
    | true =>
      simp only [d69517, d73227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8609 q ha hb
  have h7 (q : Pattern) (ha : d4837 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8607 q ha hb
    | true =>
      simp only [d4837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8602 q ha hb
  have h8 (q : Pattern) (ha : d69996 q = 1) (hb : d73190 q = 1) : d73228 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69996, d73228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69996, d73228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69997 q = 1) (hb : d73190 q = 1) : d73229 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69997, d73229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69997, d73229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d69998 q = 1) (hb : d73190 q = 1) : d73230 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69998, d73230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69998, d73230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69524 q = 1) (hb : d73190 q = 1) : d69524 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8603 q ha hb
  have h13 (q : Pattern) (ha : d69999 q = 1) (hb : d73190 q = 1) : d69525 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69999, d69525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69999, d69525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70000 q = 1) (hb : d73190 q = 1) : d69526 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70000, d69526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70000, d69526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d70001 q = 1) (hb : d73190 q = 1) : d69527 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70001, d69527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d70001, d69527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d70002 q = 1) (hb : d73190 q = 1) : d73231 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70002, d73231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70002, d73231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69534 q = 1) (hb : d73190 q = 1) : d69534 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8604 q ha hb
  have h19 (q : Pattern) (ha : d70003 q = 1) (hb : d73190 q = 1) : d69535 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70003, d69535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d70003, d69535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d70004 q = 1) (hb : d73190 q = 1) : d69536 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70004, d69536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d70004, d69536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d70005 q = 1) (hb : d73190 q = 1) : d69537 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70005, d69537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d70005, d69537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d70006 q = 1) (hb : d73190 q = 1) : d69538 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70006, d69538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d70006, d69538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d70007 q = 1) (hb : d73190 q = 1) : d73232 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70007, d73232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d70007, d73232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro8611 (p : Pattern) (ha : d70013 p = 1) (hb : d73190 p = 1) : d73238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70008 q = 1) (hb : d73190 q = 1) : d73233 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70008, d73233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70008, d73233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8610 q ha hb
  have h2 (q : Pattern) (ha : d70009 q = 1) (hb : d73190 q = 1) : d73234 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70009, d73234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70009, d73234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70010 q = 1) (hb : d73190 q = 1) : d73235 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70010, d73235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70010, d73235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70011 q = 1) (hb : d73190 q = 1) : d73236 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70011, d73236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70011, d73236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70012 q = 1) (hb : d73190 q = 1) : d73237 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70012, d73237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70012, d73237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70013 q = 1) (hb : d73190 q = 1) : d73238 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70013, d73238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70013, d73238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8612 (p : Pattern) (ha : d950 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d939 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d940 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d940, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d941 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d942 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d943 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d945 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d946 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d946, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d947 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d948 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d949 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d950 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8613 (p : Pattern) (ha : d959 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d945 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d946 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d946, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d947 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d948 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d949 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d959 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8614 (p : Pattern) (ha : d1069 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1064 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1065 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1065, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1066 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1067 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1068 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1069 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8615 (p : Pattern) (ha : d4873 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d909 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4869 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4869, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4869, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4870 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4871 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4872 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4873 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8616 (p : Pattern) (ha : d4880 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d909 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4869 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4869, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4869, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4870 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4871 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4872 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d932 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4876 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4876, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4876, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d4877 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4878 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4879 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4880 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8617 (p : Pattern) (ha : d4931 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d4926 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4927 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4927, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4927, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4928 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4929 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4930 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d939 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d940 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d940, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d941 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d942 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d943 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4931 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8618 (p : Pattern) (ha : d69551 p = 1) (hb : d73190 p = 1) : d73242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d4884 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4885 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4885, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4885, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4886 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4887 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d4888 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4889 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4889, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4889, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d4890 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69548 q = 1) (hb : d73190 q = 1) : d69548 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d69549 q = 1) (hb : d73190 q = 1) : d73240 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69549, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69549, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69550 q = 1) (hb : d73190 q = 1) : d73241 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69550, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69550, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69551 q = 1) (hb : d73190 q = 1) : d73242 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69551, d73242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69551, d73242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8619 (p : Pattern) (ha : d69556 p = 1) (hb : d73190 p = 1) : d73243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d4884 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4885 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4885, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4885, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4886 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4887 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d4888 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4889 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4889, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4889, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d4890 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69548 q = 1) (hb : d73190 q = 1) : d69548 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d69549 q = 1) (hb : d73190 q = 1) : d73240 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69549, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69549, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69550 q = 1) (hb : d73190 q = 1) : d73241 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69550, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69550, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d4898 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4899 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4899, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4899, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d4900 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4901 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d4902 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d4903 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4903, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4903, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d4904 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d69553 q = 1) (hb : d73190 q = 1) : d69553 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d69554 q = 1) (hb : d73190 q = 1) : d69561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69554, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d69554, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d69555 q = 1) (hb : d73190 q = 1) : d69562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69555, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69555, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d69556 q = 1) (hb : d73190 q = 1) : d73243 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69556, d73243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69556, d73243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro8620 (p : Pattern) (ha : d70026 p = 1) (hb : d73190 p = 1) : d73249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4874 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8615 q ha hb
  have h2 (q : Pattern) (ha : d4875 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4881 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8615 q ha hb
    | true =>
      simp only [d4881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8616 q ha hb
  have h4 (q : Pattern) (ha : d4882 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4883 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69557 q = 1) (hb : d73190 q = 1) : d73244 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69557, d73244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8618 q ha hb
    | true =>
      simp only [d69557, d73244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8619 q ha hb
  have h7 (q : Pattern) (ha : d4932 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8617 q ha hb
    | true =>
      simp only [d4932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8612 q ha hb
  have h8 (q : Pattern) (ha : d70015 q = 1) (hb : d73190 q = 1) : d73245 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70015, d73245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70015, d73245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70016 q = 1) (hb : d73190 q = 1) : d73246 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70016, d73246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70016, d73246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d70017 q = 1) (hb : d73190 q = 1) : d73247 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70017, d73247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70017, d73247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69564 q = 1) (hb : d73190 q = 1) : d69564 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8613 q ha hb
  have h13 (q : Pattern) (ha : d70018 q = 1) (hb : d73190 q = 1) : d69565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70018, d69565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d70018, d69565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70019 q = 1) (hb : d73190 q = 1) : d69566 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70019, d69566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70019, d69566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d70020 q = 1) (hb : d73190 q = 1) : d69567 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70020, d69567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d70020, d69567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d70021 q = 1) (hb : d73190 q = 1) : d73248 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70021, d73248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70021, d73248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69574 q = 1) (hb : d73190 q = 1) : d69574 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8614 q ha hb
  have h19 (q : Pattern) (ha : d70022 q = 1) (hb : d73190 q = 1) : d69575 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70022, d69575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d70022, d69575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d70023 q = 1) (hb : d73190 q = 1) : d69576 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70023, d69576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d70023, d69576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d70024 q = 1) (hb : d73190 q = 1) : d69577 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70024, d69577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d70024, d69577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d70025 q = 1) (hb : d73190 q = 1) : d69578 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70025, d69578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d70025, d69578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d70026 q = 1) (hb : d73190 q = 1) : d73249 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70026, d73249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d70026, d73249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro8621 (p : Pattern) (ha : d70032 p = 1) (hb : d73190 p = 1) : d73255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70027 q = 1) (hb : d73190 q = 1) : d73250 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70027, d73250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70027, d73250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8620 q ha hb
  have h2 (q : Pattern) (ha : d70028 q = 1) (hb : d73190 q = 1) : d73251 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70028, d73251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70028, d73251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70029 q = 1) (hb : d73190 q = 1) : d73252 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70029, d73252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70029, d73252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70030 q = 1) (hb : d73190 q = 1) : d73253 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70030, d73253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70030, d73253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70031 q = 1) (hb : d73190 q = 1) : d73254 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70031, d73254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70031, d73254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70032 q = 1) (hb : d73190 q = 1) : d73255 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70032, d73255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70032, d73255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8622 (p : Pattern) (ha : d1361 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1350 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1351 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1351, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1352 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1353 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1354 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1356 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1357 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1357, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1358 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1359 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1360 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1361 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8623 (p : Pattern) (ha : d1370 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1356 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1357 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1357, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1358 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1359 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1360 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1370 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8624 (p : Pattern) (ha : d1503 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1498 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1499 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1499, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1499, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1500 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1501 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1502 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1503 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8625 (p : Pattern) (ha : d4969 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1320 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4965 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4965, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4965, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4966 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4967 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4968 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4969 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8626 (p : Pattern) (ha : d4976 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1320 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4965 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4965, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4965, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4966 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4967 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4968 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1343 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4972 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4972, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4972, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d4973 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4974 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4975 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4976 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8627 (p : Pattern) (ha : d5041 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5036 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5037 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5037, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5037, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5038 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5039 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5040 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1350 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1351 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1351, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1352 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1353 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1354 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5041 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8628 (p : Pattern) (ha : d69592 p = 1) (hb : d73190 p = 1) : d73260 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d4980 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4981 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4981, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4981, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4982 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4983 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d4984 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4985 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4985, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4985, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d4986 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69589 q = 1) (hb : d73190 q = 1) : d69589 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d69590 q = 1) (hb : d73190 q = 1) : d73258 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69590, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69590, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69591 q = 1) (hb : d73190 q = 1) : d73259 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69591, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69591, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69592 q = 1) (hb : d73190 q = 1) : d73260 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69592, d73260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69592, d73260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8629 (p : Pattern) (ha : d69597 p = 1) (hb : d73190 p = 1) : d73261 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d4980 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4981 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4981, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4981, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4982 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4983 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d4984 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4985 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4985, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4985, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d4986 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69589 q = 1) (hb : d73190 q = 1) : d69589 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d69590 q = 1) (hb : d73190 q = 1) : d73258 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69590, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69590, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69591 q = 1) (hb : d73190 q = 1) : d73259 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69591, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69591, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d4994 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4995 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4995, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4995, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d4996 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4997 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d4998 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d4999 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4999, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4999, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d5000 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d5000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d69594 q = 1) (hb : d73190 q = 1) : d69594 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d69595 q = 1) (hb : d73190 q = 1) : d69602 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69595, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d69595, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d69596 q = 1) (hb : d73190 q = 1) : d69603 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69596, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69596, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d69597 q = 1) (hb : d73190 q = 1) : d73261 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69597, d73261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69597, d73261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro8630 (p : Pattern) (ha : d70046 p = 1) (hb : d73190 p = 1) : d73267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4970 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8625 q ha hb
  have h2 (q : Pattern) (ha : d4971 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4977 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8625 q ha hb
    | true =>
      simp only [d4977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8626 q ha hb
  have h4 (q : Pattern) (ha : d4978 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4979 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69598 q = 1) (hb : d73190 q = 1) : d73262 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69598, d73262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8628 q ha hb
    | true =>
      simp only [d69598, d73262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8629 q ha hb
  have h7 (q : Pattern) (ha : d5042 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8627 q ha hb
    | true =>
      simp only [d5042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8622 q ha hb
  have h8 (q : Pattern) (ha : d70035 q = 1) (hb : d73190 q = 1) : d73263 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70035, d73263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70035, d73263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70036 q = 1) (hb : d73190 q = 1) : d73264 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70036, d73264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70036, d73264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d70037 q = 1) (hb : d73190 q = 1) : d73265 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70037, d73265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70037, d73265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69605 q = 1) (hb : d73190 q = 1) : d69605 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8623 q ha hb
  have h13 (q : Pattern) (ha : d70038 q = 1) (hb : d73190 q = 1) : d69606 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70038, d69606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d70038, d69606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70039 q = 1) (hb : d73190 q = 1) : d69607 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70039, d69607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70039, d69607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d70040 q = 1) (hb : d73190 q = 1) : d69608 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70040, d69608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d70040, d69608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d70041 q = 1) (hb : d73190 q = 1) : d73266 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70041, d73266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70041, d73266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69615 q = 1) (hb : d73190 q = 1) : d69615 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8624 q ha hb
  have h19 (q : Pattern) (ha : d70042 q = 1) (hb : d73190 q = 1) : d69616 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70042, d69616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d70042, d69616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d70043 q = 1) (hb : d73190 q = 1) : d69617 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70043, d69617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d70043, d69617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d70044 q = 1) (hb : d73190 q = 1) : d69618 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70044, d69618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d70044, d69618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d70045 q = 1) (hb : d73190 q = 1) : d69619 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70045, d69619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d70045, d69619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d70046 q = 1) (hb : d73190 q = 1) : d73267 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70046, d73267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d70046, d73267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro8631 (p : Pattern) (ha : d70052 p = 1) (hb : d73190 p = 1) : d73273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70047 q = 1) (hb : d73190 q = 1) : d73268 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70047, d73268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70047, d73268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8630 q ha hb
  have h2 (q : Pattern) (ha : d70048 q = 1) (hb : d73190 q = 1) : d73269 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70048, d73269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70048, d73269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70049 q = 1) (hb : d73190 q = 1) : d73270 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70049, d73270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70049, d73270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70050 q = 1) (hb : d73190 q = 1) : d73271 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70050, d73271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70050, d73271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70051 q = 1) (hb : d73190 q = 1) : d73272 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70051, d73272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70051, d73272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70052 q = 1) (hb : d73190 q = 1) : d73273 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70052, d73273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70052, d73273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8632 (p : Pattern) (ha : d1838 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1827 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1828 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1828, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1829 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1830 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1831 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1833 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1834 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1834, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1835 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1836 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1837 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1838 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8633 (p : Pattern) (ha : d1847 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1833 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1834 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1834, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1835 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1836 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1837 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1847 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8634 (p : Pattern) (ha : d1980 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1975 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1976 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1976, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1976, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1977 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1978 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1979 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1980 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8635 (p : Pattern) (ha : d5080 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1797 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5076 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5076, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5076, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5077 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5078 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5079 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5080 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8636 (p : Pattern) (ha : d5087 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1797 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5076 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5076, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5076, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5077 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5078 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5079 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1820 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5083 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5083, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5083, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d5084 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5085 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5086 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5087 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8637 (p : Pattern) (ha : d5157 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5152 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5153 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5153, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5153, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5154 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5155 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5156 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1827 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1828 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1828, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1829 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1830 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1831 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5157 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8638 (p : Pattern) (ha : d69634 p = 1) (hb : d73190 p = 1) : d73279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5091 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5092 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5092, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5092, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5093 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5094 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5095 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5096 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5096, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5096, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d5097 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69631 q = 1) (hb : d73190 q = 1) : d69631 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d69632 q = 1) (hb : d73190 q = 1) : d73277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69632, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69632, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69633 q = 1) (hb : d73190 q = 1) : d73278 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69633, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69633, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69634 q = 1) (hb : d73190 q = 1) : d73279 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69634, d73279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69634, d73279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8639 (p : Pattern) (ha : d69639 p = 1) (hb : d73190 p = 1) : d73280 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5091 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5092 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5092, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5092, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5093 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5094 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5095 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5096 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5096, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5096, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d5097 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69631 q = 1) (hb : d73190 q = 1) : d69631 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d69632 q = 1) (hb : d73190 q = 1) : d73277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69632, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69632, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69633 q = 1) (hb : d73190 q = 1) : d73278 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69633, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69633, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d5105 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d5106 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5106, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5106, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d5107 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d5108 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d5109 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d5110 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5110, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5110, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d5111 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d5111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d69636 q = 1) (hb : d73190 q = 1) : d69636 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d69637 q = 1) (hb : d73190 q = 1) : d69644 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69637, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d69637, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d69638 q = 1) (hb : d73190 q = 1) : d69645 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69638, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69638, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d69639 q = 1) (hb : d73190 q = 1) : d73280 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69639, d73280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69639, d73280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro8640 (p : Pattern) (ha : d70067 p = 1) (hb : d73190 p = 1) : d73286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5081 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8635 q ha hb
  have h2 (q : Pattern) (ha : d5082 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5088 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8635 q ha hb
    | true =>
      simp only [d5088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8636 q ha hb
  have h4 (q : Pattern) (ha : d5089 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5090 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d5090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69640 q = 1) (hb : d73190 q = 1) : d73281 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69640, d73281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8638 q ha hb
    | true =>
      simp only [d69640, d73281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8639 q ha hb
  have h7 (q : Pattern) (ha : d5158 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8637 q ha hb
    | true =>
      simp only [d5158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8632 q ha hb
  have h8 (q : Pattern) (ha : d70056 q = 1) (hb : d73190 q = 1) : d73282 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70056, d73282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70056, d73282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70057 q = 1) (hb : d73190 q = 1) : d73283 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70057, d73283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70057, d73283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d70058 q = 1) (hb : d73190 q = 1) : d73284 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70058, d73284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70058, d73284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69647 q = 1) (hb : d73190 q = 1) : d69647 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8633 q ha hb
  have h13 (q : Pattern) (ha : d70059 q = 1) (hb : d73190 q = 1) : d69648 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70059, d69648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d70059, d69648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70060 q = 1) (hb : d73190 q = 1) : d69649 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70060, d69649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70060, d69649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d70061 q = 1) (hb : d73190 q = 1) : d69650 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70061, d69650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d70061, d69650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d70062 q = 1) (hb : d73190 q = 1) : d73285 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70062, d73285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70062, d73285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69657 q = 1) (hb : d73190 q = 1) : d69657 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8634 q ha hb
  have h19 (q : Pattern) (ha : d70063 q = 1) (hb : d73190 q = 1) : d69658 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70063, d69658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d70063, d69658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d70064 q = 1) (hb : d73190 q = 1) : d69659 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70064, d69659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d70064, d69659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d70065 q = 1) (hb : d73190 q = 1) : d69660 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70065, d69660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d70065, d69660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d70066 q = 1) (hb : d73190 q = 1) : d69661 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70066, d69661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d70066, d69661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d70067 q = 1) (hb : d73190 q = 1) : d73286 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70067, d73286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d70067, d73286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro8641 (p : Pattern) (ha : d70073 p = 1) (hb : d73190 p = 1) : d73292 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70068 q = 1) (hb : d73190 q = 1) : d73287 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70068, d73287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70068, d73287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8640 q ha hb
  have h2 (q : Pattern) (ha : d70069 q = 1) (hb : d73190 q = 1) : d73288 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70069, d73288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70069, d73288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70070 q = 1) (hb : d73190 q = 1) : d73289 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70070, d73289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70070, d73289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70071 q = 1) (hb : d73190 q = 1) : d73290 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70071, d73290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70071, d73290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70072 q = 1) (hb : d73190 q = 1) : d73291 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70072, d73291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70072, d73291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70073 q = 1) (hb : d73190 q = 1) : d73292 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70073, d73292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70073, d73292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8642 (p : Pattern) (ha : d2316 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2305 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2306 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2306, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2307 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2308 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2309 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2311 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2312 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2312, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2313 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2314 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2315 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2316 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8643 (p : Pattern) (ha : d2325 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2312 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2312, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2313 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2314 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2315 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2325 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8644 (p : Pattern) (ha : d2458 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2453 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2454 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2454, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2454, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2455 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2456 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2457 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2458 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8645 (p : Pattern) (ha : d5197 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2275 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5193 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5193, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5193, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5194 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5195 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5196 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5197 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8646 (p : Pattern) (ha : d5204 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2275 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5193 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5193, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5193, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5194 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5195 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5196 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2298 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5200 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5200, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5200, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d5201 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5202 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5203 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5204 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8647 (p : Pattern) (ha : d5270 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5265 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5266 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5266, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5266, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5267 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5268 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5269 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2305 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2306 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2306, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2307 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2308 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2309 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5270 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8648 (p : Pattern) (ha : d69677 p = 1) (hb : d73190 p = 1) : d73299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5208 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5209 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5209, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5209, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5210 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5211 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5212 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5213 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5213, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5213, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d5214 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69674 q = 1) (hb : d73190 q = 1) : d69674 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d69675 q = 1) (hb : d73190 q = 1) : d73297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69675, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69675, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69676 q = 1) (hb : d73190 q = 1) : d73298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69676, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69676, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69677 q = 1) (hb : d73190 q = 1) : d73299 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69677, d73299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69677, d73299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8649 (p : Pattern) (ha : d69682 p = 1) (hb : d73190 p = 1) : d73300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5208 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5209 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5209, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5209, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5210 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5211 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5212 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5213 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5213, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5213, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d5214 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69674 q = 1) (hb : d73190 q = 1) : d69674 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d69675 q = 1) (hb : d73190 q = 1) : d73297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69675, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69675, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69676 q = 1) (hb : d73190 q = 1) : d73298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69676, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69676, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d5222 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d5223 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5223, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5223, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d5224 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d5225 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d5226 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d5227 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5227, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5227, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d5228 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d5228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d69679 q = 1) (hb : d73190 q = 1) : d69679 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d69680 q = 1) (hb : d73190 q = 1) : d69687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69680, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d69680, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d69681 q = 1) (hb : d73190 q = 1) : d69688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69681, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69681, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d69682 q = 1) (hb : d73190 q = 1) : d73300 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69682, d73300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69682, d73300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro8650 (p : Pattern) (ha : d70089 p = 1) (hb : d73190 p = 1) : d73306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5198 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8645 q ha hb
  have h2 (q : Pattern) (ha : d5199 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5205 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8645 q ha hb
    | true =>
      simp only [d5205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8646 q ha hb
  have h4 (q : Pattern) (ha : d5206 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5207 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d5207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69683 q = 1) (hb : d73190 q = 1) : d73301 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69683, d73301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8648 q ha hb
    | true =>
      simp only [d69683, d73301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8649 q ha hb
  have h7 (q : Pattern) (ha : d5271 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8647 q ha hb
    | true =>
      simp only [d5271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8642 q ha hb
  have h8 (q : Pattern) (ha : d70078 q = 1) (hb : d73190 q = 1) : d73302 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70078, d73302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70078, d73302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70079 q = 1) (hb : d73190 q = 1) : d73303 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70079, d73303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70079, d73303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d70080 q = 1) (hb : d73190 q = 1) : d73304 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70080, d73304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70080, d73304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69690 q = 1) (hb : d73190 q = 1) : d69690 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8643 q ha hb
  have h13 (q : Pattern) (ha : d70081 q = 1) (hb : d73190 q = 1) : d69691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70081, d69691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d70081, d69691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70082 q = 1) (hb : d73190 q = 1) : d69692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70082, d69692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70082, d69692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d70083 q = 1) (hb : d73190 q = 1) : d69693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70083, d69693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d70083, d69693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d70084 q = 1) (hb : d73190 q = 1) : d73305 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70084, d73305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70084, d73305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69700 q = 1) (hb : d73190 q = 1) : d69700 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8644 q ha hb
  have h19 (q : Pattern) (ha : d70085 q = 1) (hb : d73190 q = 1) : d69701 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70085, d69701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d70085, d69701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d70086 q = 1) (hb : d73190 q = 1) : d69702 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70086, d69702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d70086, d69702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d70087 q = 1) (hb : d73190 q = 1) : d69703 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70087, d69703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d70087, d69703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d70088 q = 1) (hb : d73190 q = 1) : d69704 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70088, d69704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d70088, d69704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d70089 q = 1) (hb : d73190 q = 1) : d73306 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70089, d73306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d70089, d73306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro8651 (p : Pattern) (ha : d70095 p = 1) (hb : d73190 p = 1) : d73312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70090 q = 1) (hb : d73190 q = 1) : d73307 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70090, d73307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70090, d73307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8650 q ha hb
  have h2 (q : Pattern) (ha : d70091 q = 1) (hb : d73190 q = 1) : d73308 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70091, d73308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70091, d73308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70092 q = 1) (hb : d73190 q = 1) : d73309 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70092, d73309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70092, d73309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70093 q = 1) (hb : d73190 q = 1) : d73310 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70093, d73310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70093, d73310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70094 q = 1) (hb : d73190 q = 1) : d73311 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70094, d73311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70094, d73311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70095 q = 1) (hb : d73190 q = 1) : d73312 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70095, d73312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70095, d73312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8652 (p : Pattern) (ha : d70101 p = 1) (hb : d73190 p = 1) : d73318 p = 1 := by
  have h0 (q : Pattern) (ha : d70014 q = 1) (hb : d73190 q = 1) : d73239 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70014, d73239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8601 q ha hb
    | true =>
      simp only [d70014, d73239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8611 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70033 q = 1) (hb : d73190 q = 1) : d73256 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70033, d73256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70033, d73256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8621 q ha hb
  have h3 (q : Pattern) (ha : d70034 q = 1) (hb : d73190 q = 1) : d73257 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70034, d73257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70034, d73257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70053 q = 1) (hb : d73190 q = 1) : d73274 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70053, d73274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70053, d73274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8631 q ha hb
  have h5 (q : Pattern) (ha : d70054 q = 1) (hb : d73190 q = 1) : d73275 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70054, d73275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70054, d73275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70055 q = 1) (hb : d73190 q = 1) : d73276 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d70055, d73276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70055, d73276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70074 q = 1) (hb : d73190 q = 1) : d73293 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70074, d73293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70074, d73293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8641 q ha hb
  have h8 (q : Pattern) (ha : d70075 q = 1) (hb : d73190 q = 1) : d73294 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70075, d73294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70075, d73294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70076 q = 1) (hb : d73190 q = 1) : d73295 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d70076, d73295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70076, d73295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70077 q = 1) (hb : d73190 q = 1) : d73296 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d70077, d73296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70077, d73296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d70096 q = 1) (hb : d73190 q = 1) : d73313 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70096, d73313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70096, d73313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8651 q ha hb
  have h12 (q : Pattern) (ha : d70097 q = 1) (hb : d73190 q = 1) : d73314 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70097, d73314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70097, d73314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d70098 q = 1) (hb : d73190 q = 1) : d73315 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d70098, d73315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70098, d73315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70099 q = 1) (hb : d73190 q = 1) : d73316 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d70099, d73316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70099, d73316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d70100 q = 1) (hb : d73190 q = 1) : d73317 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d70100, d73317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70100, d73317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d70101 q = 1) (hb : d73190 q = 1) : d73318 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d70101, d73318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d70101, d73318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro8653 (p : Pattern) (ha : d70107 p = 1) (hb : d73190 p = 1) : d73324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70102 q = 1) (hb : d73190 q = 1) : d73319 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d70102, d73319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8652 q ha hb
    | true =>
      simp only [d70102, d73319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70103 q = 1) (hb : d73190 q = 1) : d73320 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d70103, d73320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70103, d73320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70104 q = 1) (hb : d73190 q = 1) : d73321 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d70104, d73321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70104, d73321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70105 q = 1) (hb : d73190 q = 1) : d73322 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d70105, d73322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70105, d73322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70106 q = 1) (hb : d73190 q = 1) : d73323 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d70106, d73323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70106, d73323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70107 q = 1) (hb : d73190 q = 1) : d73324 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d70107, d73324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70107, d73324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8654 (p : Pattern) (ha : d70113 p = 1) (hb : d73190 p = 1) : d73330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70108 q = 1) (hb : d73190 q = 1) : d73325 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d70108, d73325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8653 q ha hb
    | true =>
      simp only [d70108, d73325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70109 q = 1) (hb : d73190 q = 1) : d73326 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d70109, d73326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70109, d73326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70110 q = 1) (hb : d73190 q = 1) : d73327 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d70110, d73327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70110, d73327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70111 q = 1) (hb : d73190 q = 1) : d73328 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d70111, d73328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70111, d73328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70112 q = 1) (hb : d73190 q = 1) : d73329 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d70112, d73329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70112, d73329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70113 q = 1) (hb : d73190 q = 1) : d73330 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d70113, d73330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70113, d73330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8655 (p : Pattern) (ha : d70119 p = 1) (hb : d73190 p = 1) : d73336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70114 q = 1) (hb : d73190 q = 1) : d73331 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d70114, d73331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8654 q ha hb
    | true =>
      simp only [d70114, d73331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70115 q = 1) (hb : d73190 q = 1) : d73332 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d70115, d73332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70115, d73332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70116 q = 1) (hb : d73190 q = 1) : d73333 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d70116, d73333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70116, d73333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70117 q = 1) (hb : d73190 q = 1) : d73334 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d70117, d73334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70117, d73334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70118 q = 1) (hb : d73190 q = 1) : d73335 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d70118, d73335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70118, d73335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70119 q = 1) (hb : d73190 q = 1) : d73336 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d70119, d73336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70119, d73336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8656 (p : Pattern) (ha : d70125 p = 1) (hb : d73190 p = 1) : d73342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70120 q = 1) (hb : d73190 q = 1) : d73337 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d70120, d73337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8655 q ha hb
    | true =>
      simp only [d70120, d73337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70121 q = 1) (hb : d73190 q = 1) : d73338 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d70121, d73338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70121, d73338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70122 q = 1) (hb : d73190 q = 1) : d73339 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d70122, d73339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70122, d73339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70123 q = 1) (hb : d73190 q = 1) : d73340 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d70123, d73340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70123, d73340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70124 q = 1) (hb : d73190 q = 1) : d73341 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d70124, d73341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70124, d73341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70125 q = 1) (hb : d73190 q = 1) : d73342 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d70125, d73342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70125, d73342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8657 (p : Pattern) (ha : d70131 p = 1) (hb : d73190 p = 1) : d73348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70126 q = 1) (hb : d73190 q = 1) : d73343 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d70126, d73343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8656 q ha hb
    | true =>
      simp only [d70126, d73343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70127 q = 1) (hb : d73190 q = 1) : d73344 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d70127, d73344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70127, d73344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70128 q = 1) (hb : d73190 q = 1) : d73345 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d70128, d73345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70128, d73345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70129 q = 1) (hb : d73190 q = 1) : d73346 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d70129, d73346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70129, d73346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70130 q = 1) (hb : d73190 q = 1) : d73347 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d70130, d73347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70130, d73347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70131 q = 1) (hb : d73190 q = 1) : d73348 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d70131, d73348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70131, d73348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8658 (p : Pattern) (ha : d70137 p = 1) (hb : d73190 p = 1) : d73354 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70132 q = 1) (hb : d73190 q = 1) : d73349 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d70132, d73349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8657 q ha hb
    | true =>
      simp only [d70132, d73349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70133 q = 1) (hb : d73190 q = 1) : d73350 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d70133, d73350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70133, d73350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70134 q = 1) (hb : d73190 q = 1) : d73351 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d70134, d73351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70134, d73351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70135 q = 1) (hb : d73190 q = 1) : d73352 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d70135, d73352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70135, d73352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70136 q = 1) (hb : d73190 q = 1) : d73353 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d70136, d73353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70136, d73353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70137 q = 1) (hb : d73190 q = 1) : d73354 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d70137, d73354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70137, d73354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8659 (p : Pattern) (ha : d70143 p = 1) (hb : d73190 p = 1) : d73360 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70138 q = 1) (hb : d73190 q = 1) : d73355 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d70138, d73355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8658 q ha hb
    | true =>
      simp only [d70138, d73355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70139 q = 1) (hb : d73190 q = 1) : d73356 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d70139, d73356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70139, d73356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70140 q = 1) (hb : d73190 q = 1) : d73357 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d70140, d73357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70140, d73357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70141 q = 1) (hb : d73190 q = 1) : d73358 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d70141, d73358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70141, d73358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70142 q = 1) (hb : d73190 q = 1) : d73359 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d70142, d73359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70142, d73359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70143 q = 1) (hb : d73190 q = 1) : d73360 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d70143, d73360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70143, d73360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8660 (p : Pattern) (ha : d53647 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5069 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5070 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5181 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5182 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8661 (p : Pattern) (ha : d69762 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d390 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4696 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4696, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4696, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4697 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4698 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4699 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69762 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8662 (p : Pattern) (ha : d69772 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d451 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69768 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69768, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69768, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d69769 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69770 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69771 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69772 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8663 (p : Pattern) (ha : d69778 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4701 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8595 q ha hb
    | true =>
      simp only [d4701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8596 q ha hb
  have h2 (q : Pattern) (ha : d4702 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69760 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69761 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69763 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8661 q ha hb
  have h6 (q : Pattern) (ha : d69764 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69765 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69766 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69767 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69773 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8662 q ha hb
  have h11 (q : Pattern) (ha : d69774 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69775 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69776 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69777 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69778 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8664 (p : Pattern) (ha : d69784 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8660 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69779 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8663 q ha hb
  have h7 (q : Pattern) (ha : d69780 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69781 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69782 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69783 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69784 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro8665 (p : Pattern) (ha : d69787 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d626 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4781 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4781, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4781, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4782 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4783 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4784 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69787 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8666 (p : Pattern) (ha : d69797 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d720 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69793 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69793, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69793, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d69794 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69795 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69796 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69797 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8667 (p : Pattern) (ha : d69803 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4786 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8605 q ha hb
    | true =>
      simp only [d4786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8606 q ha hb
  have h2 (q : Pattern) (ha : d4787 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69785 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69786 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69788 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8665 q ha hb
  have h6 (q : Pattern) (ha : d69789 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69790 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69791 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69792 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69798 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8666 q ha hb
  have h11 (q : Pattern) (ha : d69799 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69800 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69801 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69802 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69803 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8668 (p : Pattern) (ha : d69809 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69804 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8667 q ha hb
  have h2 (q : Pattern) (ha : d69805 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69806 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69807 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69808 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69809 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8669 (p : Pattern) (ha : d69813 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d932 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4876 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4876, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4876, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4877 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4878 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4879 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69813 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8670 (p : Pattern) (ha : d69823 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1053 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69819 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69819, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69819, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d69820 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69821 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69822 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69823 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8671 (p : Pattern) (ha : d69829 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4881 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8615 q ha hb
    | true =>
      simp only [d4881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8616 q ha hb
  have h2 (q : Pattern) (ha : d4882 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69811 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69812 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69814 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8669 q ha hb
  have h6 (q : Pattern) (ha : d69815 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69816 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69817 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69818 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69824 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8670 q ha hb
  have h11 (q : Pattern) (ha : d69825 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69826 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69827 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69828 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69829 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8672 (p : Pattern) (ha : d69835 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69830 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8671 q ha hb
  have h2 (q : Pattern) (ha : d69831 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69832 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69833 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69834 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69835 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8673 (p : Pattern) (ha : d69840 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1343 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4972 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4972, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4972, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4973 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4974 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4975 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69840 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8674 (p : Pattern) (ha : d69850 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1487 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69846 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69846, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69846, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d69847 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69848 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69849 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69850 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8675 (p : Pattern) (ha : d69856 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4977 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8625 q ha hb
    | true =>
      simp only [d4977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8626 q ha hb
  have h2 (q : Pattern) (ha : d4978 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69838 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69839 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69841 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8673 q ha hb
  have h6 (q : Pattern) (ha : d69842 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69843 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69844 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69845 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69851 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8674 q ha hb
  have h11 (q : Pattern) (ha : d69852 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69853 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69854 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69855 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69856 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8676 (p : Pattern) (ha : d69862 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69857 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8675 q ha hb
  have h2 (q : Pattern) (ha : d69858 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69859 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69860 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69861 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69862 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8677 (p : Pattern) (ha : d69868 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1820 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5083 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5083, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5083, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5084 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5085 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5086 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69868 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8678 (p : Pattern) (ha : d69878 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1964 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69874 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69874, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69874, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d69875 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69876 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69877 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69878 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8679 (p : Pattern) (ha : d69884 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5088 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8635 q ha hb
    | true =>
      simp only [d5088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8636 q ha hb
  have h2 (q : Pattern) (ha : d5089 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69866 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69867 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69869 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8677 q ha hb
  have h6 (q : Pattern) (ha : d69870 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69871 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69872 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69873 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69879 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8678 q ha hb
  have h11 (q : Pattern) (ha : d69880 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69881 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69882 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69883 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69884 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8680 (p : Pattern) (ha : d69890 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69885 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8679 q ha hb
  have h2 (q : Pattern) (ha : d69886 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69887 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69888 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69889 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69890 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8681 (p : Pattern) (ha : d69897 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2298 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5200 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5200, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5200, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5201 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5202 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5203 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69897 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8682 (p : Pattern) (ha : d69907 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2442 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69903 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69903, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69903, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d69904 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69905 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69906 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69907 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8683 (p : Pattern) (ha : d69913 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5205 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8645 q ha hb
    | true =>
      simp only [d5205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8646 q ha hb
  have h2 (q : Pattern) (ha : d5206 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69895 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69896 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69898 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8681 q ha hb
  have h6 (q : Pattern) (ha : d69899 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69900 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69901 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69902 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69908 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8682 q ha hb
  have h11 (q : Pattern) (ha : d69909 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69910 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69911 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69912 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69913 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8684 (p : Pattern) (ha : d69919 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69914 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8683 q ha hb
  have h2 (q : Pattern) (ha : d69915 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69916 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69917 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69918 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69919 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8685 (p : Pattern) (ha : d69925 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d69810 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8664 q ha hb
    | true =>
      simp only [d69810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8668 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69836 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8672 q ha hb
  have h3 (q : Pattern) (ha : d69837 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69863 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8676 q ha hb
  have h5 (q : Pattern) (ha : d69864 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69865 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69891 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8680 q ha hb
  have h8 (q : Pattern) (ha : d69892 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69893 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69894 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d69894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69920 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8684 q ha hb
  have h12 (q : Pattern) (ha : d69921 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69922 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69923 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d69923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69924 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d69924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69925 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d69925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro8686 (p : Pattern) (ha : d69931 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69926 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d69926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8685 q ha hb
    | true =>
      simp only [d69926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69927 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d69927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69928 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d69928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69929 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d69929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69930 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d69930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69931 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d69931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8687 (p : Pattern) (ha : d69937 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69932 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d69932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8686 q ha hb
    | true =>
      simp only [d69932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69933 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d69933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69934 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d69934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69935 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d69935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69936 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d69936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69937 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d69937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8688 (p : Pattern) (ha : d69943 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69938 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d69938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8687 q ha hb
    | true =>
      simp only [d69938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69939 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d69939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69940 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d69940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69941 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d69941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69942 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d69942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69943 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d69943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8689 (p : Pattern) (ha : d69949 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69944 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d69944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8688 q ha hb
    | true =>
      simp only [d69944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69945 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d69945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69946 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d69946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69947 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d69947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69948 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d69948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69949 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d69949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8690 (p : Pattern) (ha : d69955 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69950 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d69950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8689 q ha hb
    | true =>
      simp only [d69950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69951 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d69951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69952 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d69952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69953 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d69953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69954 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d69954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69955 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d69955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8691 (p : Pattern) (ha : d69961 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69956 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d69956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8690 q ha hb
    | true =>
      simp only [d69956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69957 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d69957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69958 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d69958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69959 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d69959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69960 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d69960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69961 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d69961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8692 (p : Pattern) (ha : d69967 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69962 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d69962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8691 q ha hb
    | true =>
      simp only [d69962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69963 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d69963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69964 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d69964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69965 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d69965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69966 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d69966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69967 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d69967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8693 (p : Pattern) (ha : d69436 p = 1) (hb : d74857 p = 1) : d75449 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d74857 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d74857 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d370 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d371 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d371, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d69433 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69433, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69433, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d69434 q = 1) (hb : d74857 q = 1) : d3843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69434, d3843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69434, d3843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69435 q = 1) (hb : d74857 q = 1) : d75448 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69435, d75448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69435, d75448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69436 q = 1) (hb : d74857 q = 1) : d75449 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69436, d75449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69436, d75449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8694 (p : Pattern) (ha : d69440 p = 1) (hb : d74857 p = 1) : d75451 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d74857 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d74857 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d370 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d371 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d371, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69433 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69433, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69433, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d69434 q = 1) (hb : d74857 q = 1) : d3843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69434, d3843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69434, d3843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69435 q = 1) (hb : d74857 q = 1) : d75448 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69435, d75448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69435, d75448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d198 q = 1) (hb : d74857 q = 1) : d198 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d202 q = 1) (hb : d74857 q = 1) : d202 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d390 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d391 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d391, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d69437 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69437, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69437, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d69438 q = 1) (hb : d74857 q = 1) : d3846 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69438, d3846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69438, d3846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69439 q = 1) (hb : d74857 q = 1) : d75450 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69439, d75450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69439, d75450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69440 q = 1) (hb : d74857 q = 1) : d75451 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69440, d75451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69440, d75451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8695 (p : Pattern) (ha : d69447 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d390 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d391 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d391, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69437 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69437, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69437, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69445 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69446 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69447 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8696 (p : Pattern) (ha : d69456 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d451 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d452 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d452, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d452, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d85 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69453 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69453, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69453, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69454 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69455 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69456 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8697 (p : Pattern) (ha : d69972 p = 1) (hb : d74857 p = 1) : d75457 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d74857 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69441 q = 1) (hb : d74857 q = 1) : d75452 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69441, d75452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8693 q ha hb
    | true =>
      simp only [d69441, d75452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8694 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d74857 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69968 q = 1) (hb : d74857 q = 1) : d75453 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69968, d75453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69968, d75453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69969 q = 1) (hb : d74857 q = 1) : d75454 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69969, d75454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69969, d75454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69970 q = 1) (hb : d74857 q = 1) : d75455 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69970, d75455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69970, d75455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69448 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8695 q ha hb
  have h8 (q : Pattern) (ha : d69449 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d69450 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d69451 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d69971 q = 1) (hb : d74857 q = 1) : d75456 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69971, d75456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69971, d75456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69457 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8696 q ha hb
  have h13 (q : Pattern) (ha : d69458 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d69459 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d69460 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d69460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d69461 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d69972 q = 1) (hb : d74857 q = 1) : d75457 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69972, d75457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69972, d75457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8698 (p : Pattern) (ha : d69472 p = 1) (hb : d74857 p = 1) : d75465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4707 q = 1) (hb : d74857 q = 1) : d4707 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4710 q = 1) (hb : d74857 q = 1) : d4710 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d4711 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69468 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69468, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d69468, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d371 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d69469 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69469, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69469, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d69470 q = 1) (hb : d74857 q = 1) : d75463 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69470, d75463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69470, d75463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69471 q = 1) (hb : d74857 q = 1) : d75464 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69471, d75464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69471, d75464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69472 q = 1) (hb : d74857 q = 1) : d75465 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69472, d75465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69472, d75465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8699 (p : Pattern) (ha : d69477 p = 1) (hb : d74857 p = 1) : d75468 p = 1 := by
  have h0 (q : Pattern) (ha : d4707 q = 1) (hb : d74857 q = 1) : d4707 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4710 q = 1) (hb : d74857 q = 1) : d4710 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d4711 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d69468 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69468, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d69468, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d371 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69469 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69469, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69469, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d69470 q = 1) (hb : d74857 q = 1) : d75463 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69470, d75463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69470, d75463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69471 q = 1) (hb : d74857 q = 1) : d75464 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69471, d75464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69471, d75464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4721 q = 1) (hb : d74857 q = 1) : d4721 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4724 q = 1) (hb : d74857 q = 1) : d4724 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d4725 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d69473 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69473, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d69473, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d391 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d69474 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69474, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69474, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d69475 q = 1) (hb : d74857 q = 1) : d75466 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69475, d75466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69475, d75466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69476 q = 1) (hb : d74857 q = 1) : d75467 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69476, d75467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69476, d75467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69477 q = 1) (hb : d74857 q = 1) : d75468 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69477, d75468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69477, d75468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8700 (p : Pattern) (ha : d69484 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4725 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69473 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69473, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69473, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d391 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69474 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69474, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69474, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69482 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69483 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69484 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8701 (p : Pattern) (ha : d69494 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4755 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69490 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69490, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69490, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d452 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69491 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69491, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69491, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69492 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69493 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69494 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8702 (p : Pattern) (ha : d69989 p = 1) (hb : d74857 p = 1) : d81403 p = 1 := by
  have h0 (q : Pattern) (ha : d4703 q = 1) (hb : d74857 q = 1) : d4703 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69478 q = 1) (hb : d74857 q = 1) : d75469 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69478, d75469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8698 q ha hb
    | true =>
      simp only [d69478, d75469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8699 q ha hb
  have h2 (q : Pattern) (ha : d4743 q = 1) (hb : d74857 q = 1) : d4743 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69978 q = 1) (hb : d74857 q = 1) : d81399 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69978, d81399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69978, d81399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69979 q = 1) (hb : d74857 q = 1) : d81400 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69979, d81400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69979, d81400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69980 q = 1) (hb : d74857 q = 1) : d81401 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69980, d81401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69980, d81401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69485 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8700 q ha hb
  have h8 (q : Pattern) (ha : d407 q = 1) (hb : d74857 q = 1) : d407 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d69981 q = 1) (hb : d74857 q = 1) : d59656 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69981, d59656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69981, d59656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69982 q = 1) (hb : d74857 q = 1) : d59657 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69982, d59657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69982, d59657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d69983 q = 1) (hb : d74857 q = 1) : d59658 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69983, d59658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69983, d59658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d69984 q = 1) (hb : d74857 q = 1) : d81402 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69984, d81402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69984, d81402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69495 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8701 q ha hb
  have h14 (q : Pattern) (ha : d463 q = 1) (hb : d74857 q = 1) : d463 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d69985 q = 1) (hb : d74857 q = 1) : d59660 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69985, d59660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69985, d59660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69986 q = 1) (hb : d74857 q = 1) : d59661 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69986, d59661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69986, d59661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d69987 q = 1) (hb : d74857 q = 1) : d59662 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69987, d59662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d69987, d59662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d69988 q = 1) (hb : d74857 q = 1) : d59663 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69988, d59663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d69988, d59663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d69989 q = 1) (hb : d74857 q = 1) : d81403 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69989, d81403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69989, d81403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8703 (p : Pattern) (ha : d69995 p = 1) (hb : d74857 p = 1) : d81409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7016 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69973 q = 1) (hb : d74857 q = 1) : d75458 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69973, d75458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69973, d75458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8697 q ha hb
  have h6 (q : Pattern) (ha : d69974 q = 1) (hb : d74857 q = 1) : d75459 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69974, d75459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69974, d75459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69975 q = 1) (hb : d74857 q = 1) : d75460 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69975, d75460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69975, d75460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69976 q = 1) (hb : d74857 q = 1) : d75461 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69976, d75461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69976, d75461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69977 q = 1) (hb : d74857 q = 1) : d75462 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69977, d75462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69977, d75462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69990 q = 1) (hb : d74857 q = 1) : d81404 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69990, d81404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69990, d81404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8702 q ha hb
  have h11 (q : Pattern) (ha : d69991 q = 1) (hb : d74857 q = 1) : d81405 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69991, d81405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69991, d81405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69992 q = 1) (hb : d74857 q = 1) : d81406 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69992, d81406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69992, d81406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69993 q = 1) (hb : d74857 q = 1) : d81407 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69993, d81407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69993, d81407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69994 q = 1) (hb : d74857 q = 1) : d81408 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69994, d81408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69994, d81408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69995 q = 1) (hb : d74857 q = 1) : d81409 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69995, d81409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69995, d81409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8704 (p : Pattern) (ha : d69511 p = 1) (hb : d74857 p = 1) : d75483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4792 q = 1) (hb : d74857 q = 1) : d4792 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4795 q = 1) (hb : d74857 q = 1) : d4795 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d4796 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69507 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69507, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d69507, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d604 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d69508 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69508, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69508, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d69509 q = 1) (hb : d74857 q = 1) : d75481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69509, d75481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69509, d75481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69510 q = 1) (hb : d74857 q = 1) : d75482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69510, d75482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69510, d75482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69511 q = 1) (hb : d74857 q = 1) : d75483 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69511, d75483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69511, d75483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8705 (p : Pattern) (ha : d69516 p = 1) (hb : d74857 p = 1) : d75486 p = 1 := by
  have h0 (q : Pattern) (ha : d4792 q = 1) (hb : d74857 q = 1) : d4792 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4795 q = 1) (hb : d74857 q = 1) : d4795 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d4796 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d69507 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69507, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d69507, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d604 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69508 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69508, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69508, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d69509 q = 1) (hb : d74857 q = 1) : d75481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69509, d75481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69509, d75481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69510 q = 1) (hb : d74857 q = 1) : d75482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69510, d75482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69510, d75482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4806 q = 1) (hb : d74857 q = 1) : d4806 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4809 q = 1) (hb : d74857 q = 1) : d4809 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d4810 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d69512 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69512, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d69512, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d627 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d69513 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69513, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69513, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d69514 q = 1) (hb : d74857 q = 1) : d75484 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69514, d75484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69514, d75484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69515 q = 1) (hb : d74857 q = 1) : d75485 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69515, d75485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69515, d75485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69516 q = 1) (hb : d74857 q = 1) : d75486 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69516, d75486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69516, d75486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8706 (p : Pattern) (ha : d69523 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4810 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69512 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69512, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69512, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d627 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69513 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69513, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69513, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69521 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69522 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69523 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8707 (p : Pattern) (ha : d69533 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4849 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69529 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69529, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69529, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d721 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69530 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69530, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69530, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69531 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69532 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69533 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8708 (p : Pattern) (ha : d70007 p = 1) (hb : d74857 p = 1) : d81414 p = 1 := by
  have h0 (q : Pattern) (ha : d4788 q = 1) (hb : d74857 q = 1) : d4788 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69517 q = 1) (hb : d74857 q = 1) : d75487 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69517, d75487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8704 q ha hb
    | true =>
      simp only [d69517, d75487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8705 q ha hb
  have h2 (q : Pattern) (ha : d4837 q = 1) (hb : d74857 q = 1) : d4837 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69996 q = 1) (hb : d74857 q = 1) : d81410 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69996, d81410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69996, d81410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69997 q = 1) (hb : d74857 q = 1) : d81411 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69997, d81411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69997, d81411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69998 q = 1) (hb : d74857 q = 1) : d81412 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69998, d81412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69998, d81412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69524 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8706 q ha hb
  have h8 (q : Pattern) (ha : d654 q = 1) (hb : d74857 q = 1) : d654 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d69999 q = 1) (hb : d74857 q = 1) : d59676 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69999, d59676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69999, d59676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70000 q = 1) (hb : d74857 q = 1) : d59677 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70000, d59677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70000, d59677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d70001 q = 1) (hb : d74857 q = 1) : d59678 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70001, d59678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70001, d59678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d70002 q = 1) (hb : d74857 q = 1) : d81413 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70002, d81413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70002, d81413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69534 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8707 q ha hb
  have h14 (q : Pattern) (ha : d737 q = 1) (hb : d74857 q = 1) : d737 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d70003 q = 1) (hb : d74857 q = 1) : d59680 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70003, d59680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70003, d59680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d70004 q = 1) (hb : d74857 q = 1) : d59681 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70004, d59681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d70004, d59681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d70005 q = 1) (hb : d74857 q = 1) : d59682 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70005, d59682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d70005, d59682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d70006 q = 1) (hb : d74857 q = 1) : d59683 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70006, d59683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d70006, d59683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d70007 q = 1) (hb : d74857 q = 1) : d81414 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70007, d81414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70007, d81414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8709 (p : Pattern) (ha : d70013 p = 1) (hb : d74857 p = 1) : d81420 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70008 q = 1) (hb : d74857 q = 1) : d81415 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70008, d81415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70008, d81415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8708 q ha hb
  have h2 (q : Pattern) (ha : d70009 q = 1) (hb : d74857 q = 1) : d81416 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70009, d81416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70009, d81416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70010 q = 1) (hb : d74857 q = 1) : d81417 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70010, d81417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70010, d81417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70011 q = 1) (hb : d74857 q = 1) : d81418 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70011, d81418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70011, d81418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70012 q = 1) (hb : d74857 q = 1) : d81419 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70012, d81419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70012, d81419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70013 q = 1) (hb : d74857 q = 1) : d81420 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70013, d81420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70013, d81420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8710 (p : Pattern) (ha : d69551 p = 1) (hb : d74857 p = 1) : d75502 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4887 q = 1) (hb : d74857 q = 1) : d4887 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4890 q = 1) (hb : d74857 q = 1) : d4890 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d4891 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69547 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69547, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d69547, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d910 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d69548 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69548, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69548, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d69549 q = 1) (hb : d74857 q = 1) : d75500 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69549, d75500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69549, d75500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69550 q = 1) (hb : d74857 q = 1) : d75501 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69550, d75501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69550, d75501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69551 q = 1) (hb : d74857 q = 1) : d75502 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69551, d75502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69551, d75502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8711 (p : Pattern) (ha : d69556 p = 1) (hb : d74857 p = 1) : d75505 p = 1 := by
  have h0 (q : Pattern) (ha : d4887 q = 1) (hb : d74857 q = 1) : d4887 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4890 q = 1) (hb : d74857 q = 1) : d4890 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d4891 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d69547 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69547, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d69547, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d910 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69548 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69548, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69548, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d69549 q = 1) (hb : d74857 q = 1) : d75500 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69549, d75500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69549, d75500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69550 q = 1) (hb : d74857 q = 1) : d75501 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69550, d75501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69550, d75501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4901 q = 1) (hb : d74857 q = 1) : d4901 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4904 q = 1) (hb : d74857 q = 1) : d4904 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d4905 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d69552 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69552, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d69552, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d933 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d69553 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69553, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69553, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d69554 q = 1) (hb : d74857 q = 1) : d75503 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69554, d75503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69554, d75503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69555 q = 1) (hb : d74857 q = 1) : d75504 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69555, d75504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69555, d75504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69556 q = 1) (hb : d74857 q = 1) : d75505 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69556, d75505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69556, d75505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8712 (p : Pattern) (ha : d69563 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4905 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69552 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69552, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69552, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d933 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69553 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69553, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69553, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69561 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69562 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69563 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8713 (p : Pattern) (ha : d69573 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4944 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69569 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69569, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69569, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1054 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69570 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69570, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69570, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69571 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69572 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69573 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8714 (p : Pattern) (ha : d70026 p = 1) (hb : d74857 p = 1) : d81426 p = 1 := by
  have h0 (q : Pattern) (ha : d4883 q = 1) (hb : d74857 q = 1) : d4883 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69557 q = 1) (hb : d74857 q = 1) : d75506 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69557, d75506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8710 q ha hb
    | true =>
      simp only [d69557, d75506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8711 q ha hb
  have h2 (q : Pattern) (ha : d4932 q = 1) (hb : d74857 q = 1) : d4932 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d70015 q = 1) (hb : d74857 q = 1) : d81422 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70015, d81422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70015, d81422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d70016 q = 1) (hb : d74857 q = 1) : d81423 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70016, d81423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70016, d81423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70017 q = 1) (hb : d74857 q = 1) : d81424 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70017, d81424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70017, d81424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69564 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8712 q ha hb
  have h8 (q : Pattern) (ha : d960 q = 1) (hb : d74857 q = 1) : d960 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d70018 q = 1) (hb : d74857 q = 1) : d59697 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70018, d59697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d70018, d59697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70019 q = 1) (hb : d74857 q = 1) : d59698 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70019, d59698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70019, d59698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d70020 q = 1) (hb : d74857 q = 1) : d59699 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70020, d59699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70020, d59699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d70021 q = 1) (hb : d74857 q = 1) : d81425 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70021, d81425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70021, d81425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69574 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8713 q ha hb
  have h14 (q : Pattern) (ha : d1070 q = 1) (hb : d74857 q = 1) : d1070 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d70022 q = 1) (hb : d74857 q = 1) : d59701 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70022, d59701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70022, d59701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d70023 q = 1) (hb : d74857 q = 1) : d59702 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70023, d59702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d70023, d59702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d70024 q = 1) (hb : d74857 q = 1) : d59703 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70024, d59703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d70024, d59703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d70025 q = 1) (hb : d74857 q = 1) : d59704 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70025, d59704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d70025, d59704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d70026 q = 1) (hb : d74857 q = 1) : d81426 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70026, d81426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70026, d81426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8715 (p : Pattern) (ha : d70032 p = 1) (hb : d74857 p = 1) : d81432 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70027 q = 1) (hb : d74857 q = 1) : d81427 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70027, d81427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70027, d81427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8714 q ha hb
  have h2 (q : Pattern) (ha : d70028 q = 1) (hb : d74857 q = 1) : d81428 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70028, d81428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70028, d81428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70029 q = 1) (hb : d74857 q = 1) : d81429 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70029, d81429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70029, d81429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70030 q = 1) (hb : d74857 q = 1) : d81430 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70030, d81430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70030, d81430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70031 q = 1) (hb : d74857 q = 1) : d81431 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70031, d81431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70031, d81431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70032 q = 1) (hb : d74857 q = 1) : d81432 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70032, d81432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70032, d81432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8716 (p : Pattern) (ha : d69592 p = 1) (hb : d74857 p = 1) : d75522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4983 q = 1) (hb : d74857 q = 1) : d4983 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4986 q = 1) (hb : d74857 q = 1) : d4986 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d4987 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69588 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69588, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d69588, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1321 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d69589 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69589, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69589, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d69590 q = 1) (hb : d74857 q = 1) : d75520 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69590, d75520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69590, d75520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69591 q = 1) (hb : d74857 q = 1) : d75521 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69591, d75521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69591, d75521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69592 q = 1) (hb : d74857 q = 1) : d75522 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69592, d75522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69592, d75522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8717 (p : Pattern) (ha : d69597 p = 1) (hb : d74857 p = 1) : d75525 p = 1 := by
  have h0 (q : Pattern) (ha : d4983 q = 1) (hb : d74857 q = 1) : d4983 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4986 q = 1) (hb : d74857 q = 1) : d4986 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d4987 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d69588 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69588, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d69588, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1321 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69589 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69589, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69589, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d69590 q = 1) (hb : d74857 q = 1) : d75520 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69590, d75520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69590, d75520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69591 q = 1) (hb : d74857 q = 1) : d75521 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69591, d75521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69591, d75521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4997 q = 1) (hb : d74857 q = 1) : d4997 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5000 q = 1) (hb : d74857 q = 1) : d5000 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d5001 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d69593 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69593, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d69593, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d1344 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d69594 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69594, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69594, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d69595 q = 1) (hb : d74857 q = 1) : d75523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69595, d75523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69595, d75523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69596 q = 1) (hb : d74857 q = 1) : d75524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69596, d75524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69596, d75524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69597 q = 1) (hb : d74857 q = 1) : d75525 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69597, d75525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69597, d75525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8718 (p : Pattern) (ha : d69604 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5001 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69593 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69593, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69593, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1344 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69594 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69594, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69594, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69602 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69603 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69604 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8719 (p : Pattern) (ha : d69614 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5054 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69610 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69610, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69610, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1488 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69611 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69611, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69611, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69612 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69613 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69614 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8720 (p : Pattern) (ha : d70046 p = 1) (hb : d74857 p = 1) : d81439 p = 1 := by
  have h0 (q : Pattern) (ha : d4979 q = 1) (hb : d74857 q = 1) : d4979 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69598 q = 1) (hb : d74857 q = 1) : d75526 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69598, d75526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8716 q ha hb
    | true =>
      simp only [d69598, d75526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8717 q ha hb
  have h2 (q : Pattern) (ha : d5042 q = 1) (hb : d74857 q = 1) : d5042 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d70035 q = 1) (hb : d74857 q = 1) : d81435 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70035, d81435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70035, d81435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d70036 q = 1) (hb : d74857 q = 1) : d81436 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70036, d81436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70036, d81436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70037 q = 1) (hb : d74857 q = 1) : d81437 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70037, d81437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70037, d81437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69605 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8718 q ha hb
  have h8 (q : Pattern) (ha : d1371 q = 1) (hb : d74857 q = 1) : d1371 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d70038 q = 1) (hb : d74857 q = 1) : d59719 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70038, d59719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d70038, d59719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70039 q = 1) (hb : d74857 q = 1) : d59720 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70039, d59720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70039, d59720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d70040 q = 1) (hb : d74857 q = 1) : d59721 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70040, d59721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70040, d59721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d70041 q = 1) (hb : d74857 q = 1) : d81438 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70041, d81438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70041, d81438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69615 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8719 q ha hb
  have h14 (q : Pattern) (ha : d1504 q = 1) (hb : d74857 q = 1) : d1504 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d70042 q = 1) (hb : d74857 q = 1) : d59723 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70042, d59723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70042, d59723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d70043 q = 1) (hb : d74857 q = 1) : d59724 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70043, d59724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d70043, d59724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d70044 q = 1) (hb : d74857 q = 1) : d59725 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70044, d59725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d70044, d59725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d70045 q = 1) (hb : d74857 q = 1) : d59726 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70045, d59726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d70045, d59726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d70046 q = 1) (hb : d74857 q = 1) : d81439 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70046, d81439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70046, d81439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8721 (p : Pattern) (ha : d70052 p = 1) (hb : d74857 p = 1) : d81445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70047 q = 1) (hb : d74857 q = 1) : d81440 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70047, d81440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70047, d81440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8720 q ha hb
  have h2 (q : Pattern) (ha : d70048 q = 1) (hb : d74857 q = 1) : d81441 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70048, d81441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70048, d81441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70049 q = 1) (hb : d74857 q = 1) : d81442 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70049, d81442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70049, d81442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70050 q = 1) (hb : d74857 q = 1) : d81443 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70050, d81443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70050, d81443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70051 q = 1) (hb : d74857 q = 1) : d81444 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70051, d81444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70051, d81444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70052 q = 1) (hb : d74857 q = 1) : d81445 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70052, d81445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70052, d81445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8722 (p : Pattern) (ha : d69634 p = 1) (hb : d74857 p = 1) : d75543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5094 q = 1) (hb : d74857 q = 1) : d5094 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5097 q = 1) (hb : d74857 q = 1) : d5097 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5098 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69630 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69630, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d69630, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1798 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d69631 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69631, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69631, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d69632 q = 1) (hb : d74857 q = 1) : d75541 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69632, d75541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69632, d75541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69633 q = 1) (hb : d74857 q = 1) : d75542 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69633, d75542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69633, d75542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69634 q = 1) (hb : d74857 q = 1) : d75543 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69634, d75543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69634, d75543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8723 (p : Pattern) (ha : d69639 p = 1) (hb : d74857 p = 1) : d75546 p = 1 := by
  have h0 (q : Pattern) (ha : d5094 q = 1) (hb : d74857 q = 1) : d5094 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5097 q = 1) (hb : d74857 q = 1) : d5097 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5098 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d69630 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69630, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d69630, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1798 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69631 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69631, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69631, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d69632 q = 1) (hb : d74857 q = 1) : d75541 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69632, d75541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69632, d75541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69633 q = 1) (hb : d74857 q = 1) : d75542 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69633, d75542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69633, d75542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5108 q = 1) (hb : d74857 q = 1) : d5108 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5111 q = 1) (hb : d74857 q = 1) : d5111 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d5112 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d69635 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69635, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d69635, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d1821 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d69636 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69636, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69636, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d69637 q = 1) (hb : d74857 q = 1) : d75544 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69637, d75544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69637, d75544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69638 q = 1) (hb : d74857 q = 1) : d75545 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69638, d75545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69638, d75545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69639 q = 1) (hb : d74857 q = 1) : d75546 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69639, d75546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69639, d75546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8724 (p : Pattern) (ha : d69646 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5112 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69635 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69635, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69635, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1821 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69636 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69636, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69636, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69644 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69645 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69646 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8725 (p : Pattern) (ha : d69656 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5170 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69652 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69652, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69652, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1965 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69653 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69653, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69653, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69654 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69655 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69656 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8726 (p : Pattern) (ha : d70067 p = 1) (hb : d74857 p = 1) : d81453 p = 1 := by
  have h0 (q : Pattern) (ha : d5090 q = 1) (hb : d74857 q = 1) : d5090 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69640 q = 1) (hb : d74857 q = 1) : d75547 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69640, d75547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8722 q ha hb
    | true =>
      simp only [d69640, d75547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8723 q ha hb
  have h2 (q : Pattern) (ha : d5158 q = 1) (hb : d74857 q = 1) : d5158 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d70056 q = 1) (hb : d74857 q = 1) : d81449 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70056, d81449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70056, d81449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d70057 q = 1) (hb : d74857 q = 1) : d81450 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70057, d81450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70057, d81450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70058 q = 1) (hb : d74857 q = 1) : d81451 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70058, d81451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70058, d81451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69647 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8724 q ha hb
  have h8 (q : Pattern) (ha : d1848 q = 1) (hb : d74857 q = 1) : d1848 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d70059 q = 1) (hb : d74857 q = 1) : d59742 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70059, d59742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d70059, d59742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70060 q = 1) (hb : d74857 q = 1) : d59743 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70060, d59743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70060, d59743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d70061 q = 1) (hb : d74857 q = 1) : d59744 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70061, d59744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70061, d59744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d70062 q = 1) (hb : d74857 q = 1) : d81452 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70062, d81452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70062, d81452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69657 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8725 q ha hb
  have h14 (q : Pattern) (ha : d1981 q = 1) (hb : d74857 q = 1) : d1981 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d70063 q = 1) (hb : d74857 q = 1) : d59746 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70063, d59746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70063, d59746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d70064 q = 1) (hb : d74857 q = 1) : d59747 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70064, d59747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d70064, d59747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d70065 q = 1) (hb : d74857 q = 1) : d59748 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70065, d59748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d70065, d59748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d70066 q = 1) (hb : d74857 q = 1) : d59749 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70066, d59749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d70066, d59749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d70067 q = 1) (hb : d74857 q = 1) : d81453 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70067, d81453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70067, d81453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8727 (p : Pattern) (ha : d70073 p = 1) (hb : d74857 p = 1) : d81459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70068 q = 1) (hb : d74857 q = 1) : d81454 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70068, d81454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70068, d81454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8726 q ha hb
  have h2 (q : Pattern) (ha : d70069 q = 1) (hb : d74857 q = 1) : d81455 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70069, d81455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70069, d81455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70070 q = 1) (hb : d74857 q = 1) : d81456 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70070, d81456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70070, d81456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70071 q = 1) (hb : d74857 q = 1) : d81457 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70071, d81457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70071, d81457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70072 q = 1) (hb : d74857 q = 1) : d81458 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70072, d81458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70072, d81458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70073 q = 1) (hb : d74857 q = 1) : d81459 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70073, d81459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70073, d81459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8728 (p : Pattern) (ha : d69677 p = 1) (hb : d74857 p = 1) : d75565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5211 q = 1) (hb : d74857 q = 1) : d5211 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5214 q = 1) (hb : d74857 q = 1) : d5214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5215 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69673 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69673, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d69673, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2276 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d69674 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69674, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69674, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d69675 q = 1) (hb : d74857 q = 1) : d75563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69675, d75563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69675, d75563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69676 q = 1) (hb : d74857 q = 1) : d75564 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69676, d75564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69676, d75564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69677 q = 1) (hb : d74857 q = 1) : d75565 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69677, d75565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69677, d75565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8729 (p : Pattern) (ha : d69682 p = 1) (hb : d74857 p = 1) : d75568 p = 1 := by
  have h0 (q : Pattern) (ha : d5211 q = 1) (hb : d74857 q = 1) : d5211 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5214 q = 1) (hb : d74857 q = 1) : d5214 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5215 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d69673 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69673, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d69673, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2276 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69674 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69674, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69674, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d69675 q = 1) (hb : d74857 q = 1) : d75563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69675, d75563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69675, d75563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69676 q = 1) (hb : d74857 q = 1) : d75564 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69676, d75564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69676, d75564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5225 q = 1) (hb : d74857 q = 1) : d5225 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5228 q = 1) (hb : d74857 q = 1) : d5228 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d5229 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d69678 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69678, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d69678, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d2299 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d69679 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69679, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69679, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d69680 q = 1) (hb : d74857 q = 1) : d75566 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69680, d75566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69680, d75566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69681 q = 1) (hb : d74857 q = 1) : d75567 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69681, d75567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69681, d75567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69682 q = 1) (hb : d74857 q = 1) : d75568 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69682, d75568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69682, d75568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8730 (p : Pattern) (ha : d69689 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5229 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69678 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69678, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69678, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2299 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69679 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69679, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69679, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69687 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69688 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69689 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8731 (p : Pattern) (ha : d69699 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5283 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69695 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69695, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69695, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2443 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69696 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69696, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69696, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69697 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69698 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69699 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8732 (p : Pattern) (ha : d70089 p = 1) (hb : d74857 p = 1) : d81468 p = 1 := by
  have h0 (q : Pattern) (ha : d5207 q = 1) (hb : d74857 q = 1) : d5207 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69683 q = 1) (hb : d74857 q = 1) : d75569 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69683, d75569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8728 q ha hb
    | true =>
      simp only [d69683, d75569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8729 q ha hb
  have h2 (q : Pattern) (ha : d5271 q = 1) (hb : d74857 q = 1) : d5271 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d70078 q = 1) (hb : d74857 q = 1) : d81464 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70078, d81464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70078, d81464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d70079 q = 1) (hb : d74857 q = 1) : d81465 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70079, d81465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70079, d81465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70080 q = 1) (hb : d74857 q = 1) : d81466 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70080, d81466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70080, d81466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69690 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8730 q ha hb
  have h8 (q : Pattern) (ha : d2326 q = 1) (hb : d74857 q = 1) : d2326 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d70081 q = 1) (hb : d74857 q = 1) : d59766 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70081, d59766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d70081, d59766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70082 q = 1) (hb : d74857 q = 1) : d59767 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70082, d59767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70082, d59767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d70083 q = 1) (hb : d74857 q = 1) : d59768 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70083, d59768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70083, d59768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d70084 q = 1) (hb : d74857 q = 1) : d81467 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70084, d81467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70084, d81467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69700 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8731 q ha hb
  have h14 (q : Pattern) (ha : d2459 q = 1) (hb : d74857 q = 1) : d2459 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d70085 q = 1) (hb : d74857 q = 1) : d59770 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70085, d59770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70085, d59770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d70086 q = 1) (hb : d74857 q = 1) : d59771 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70086, d59771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d70086, d59771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d70087 q = 1) (hb : d74857 q = 1) : d59772 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70087, d59772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d70087, d59772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d70088 q = 1) (hb : d74857 q = 1) : d59773 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70088, d59773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d70088, d59773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d70089 q = 1) (hb : d74857 q = 1) : d81468 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70089, d81468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70089, d81468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8733 (p : Pattern) (ha : d70095 p = 1) (hb : d74857 p = 1) : d81474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70090 q = 1) (hb : d74857 q = 1) : d81469 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70090, d81469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70090, d81469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8732 q ha hb
  have h2 (q : Pattern) (ha : d70091 q = 1) (hb : d74857 q = 1) : d81470 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70091, d81470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70091, d81470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70092 q = 1) (hb : d74857 q = 1) : d81471 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70092, d81471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70092, d81471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70093 q = 1) (hb : d74857 q = 1) : d81472 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70093, d81472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70093, d81472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70094 q = 1) (hb : d74857 q = 1) : d81473 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70094, d81473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70094, d81473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70095 q = 1) (hb : d74857 q = 1) : d81474 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70095, d81474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70095, d81474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8734 (p : Pattern) (ha : d70101 p = 1) (hb : d74857 p = 1) : d81480 p = 1 := by
  have h0 (q : Pattern) (ha : d70014 q = 1) (hb : d74857 q = 1) : d81421 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70014, d81421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8703 q ha hb
    | true =>
      simp only [d70014, d81421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8709 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70033 q = 1) (hb : d74857 q = 1) : d81433 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70033, d81433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70033, d81433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8715 q ha hb
  have h3 (q : Pattern) (ha : d70034 q = 1) (hb : d74857 q = 1) : d81434 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70034, d81434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70034, d81434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70053 q = 1) (hb : d74857 q = 1) : d81446 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70053, d81446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70053, d81446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8721 q ha hb
  have h5 (q : Pattern) (ha : d70054 q = 1) (hb : d74857 q = 1) : d81447 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70054, d81447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70054, d81447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70055 q = 1) (hb : d74857 q = 1) : d81448 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d70055, d81448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70055, d81448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70074 q = 1) (hb : d74857 q = 1) : d81460 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70074, d81460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70074, d81460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8727 q ha hb
  have h8 (q : Pattern) (ha : d70075 q = 1) (hb : d74857 q = 1) : d81461 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70075, d81461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70075, d81461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70076 q = 1) (hb : d74857 q = 1) : d81462 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d70076, d81462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70076, d81462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70077 q = 1) (hb : d74857 q = 1) : d81463 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d70077, d81463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70077, d81463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d70096 q = 1) (hb : d74857 q = 1) : d81475 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70096, d81475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70096, d81475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8733 q ha hb
  have h12 (q : Pattern) (ha : d70097 q = 1) (hb : d74857 q = 1) : d81476 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70097, d81476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70097, d81476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d70098 q = 1) (hb : d74857 q = 1) : d81477 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d70098, d81477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70098, d81477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70099 q = 1) (hb : d74857 q = 1) : d81478 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d70099, d81478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70099, d81478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d70100 q = 1) (hb : d74857 q = 1) : d81479 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d70100, d81479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70100, d81479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d70101 q = 1) (hb : d74857 q = 1) : d81480 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d70101, d81480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d70101, d81480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro8735 (p : Pattern) (ha : d70107 p = 1) (hb : d74857 p = 1) : d81486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70102 q = 1) (hb : d74857 q = 1) : d81481 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d70102, d81481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8734 q ha hb
    | true =>
      simp only [d70102, d81481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70103 q = 1) (hb : d74857 q = 1) : d81482 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d70103, d81482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70103, d81482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70104 q = 1) (hb : d74857 q = 1) : d81483 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d70104, d81483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70104, d81483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70105 q = 1) (hb : d74857 q = 1) : d81484 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d70105, d81484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70105, d81484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70106 q = 1) (hb : d74857 q = 1) : d81485 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d70106, d81485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70106, d81485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70107 q = 1) (hb : d74857 q = 1) : d81486 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d70107, d81486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70107, d81486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8736 (p : Pattern) (ha : d70113 p = 1) (hb : d74857 p = 1) : d81492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70108 q = 1) (hb : d74857 q = 1) : d81487 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d70108, d81487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8735 q ha hb
    | true =>
      simp only [d70108, d81487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70109 q = 1) (hb : d74857 q = 1) : d81488 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d70109, d81488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70109, d81488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70110 q = 1) (hb : d74857 q = 1) : d81489 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d70110, d81489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70110, d81489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70111 q = 1) (hb : d74857 q = 1) : d81490 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d70111, d81490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70111, d81490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70112 q = 1) (hb : d74857 q = 1) : d81491 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d70112, d81491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70112, d81491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70113 q = 1) (hb : d74857 q = 1) : d81492 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d70113, d81492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70113, d81492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8737 (p : Pattern) (ha : d70119 p = 1) (hb : d74857 p = 1) : d81498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70114 q = 1) (hb : d74857 q = 1) : d81493 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d70114, d81493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8736 q ha hb
    | true =>
      simp only [d70114, d81493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70115 q = 1) (hb : d74857 q = 1) : d81494 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d70115, d81494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70115, d81494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70116 q = 1) (hb : d74857 q = 1) : d81495 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d70116, d81495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70116, d81495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70117 q = 1) (hb : d74857 q = 1) : d81496 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d70117, d81496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70117, d81496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70118 q = 1) (hb : d74857 q = 1) : d81497 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d70118, d81497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70118, d81497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70119 q = 1) (hb : d74857 q = 1) : d81498 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d70119, d81498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70119, d81498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8738 (p : Pattern) (ha : d70125 p = 1) (hb : d74857 p = 1) : d81504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70120 q = 1) (hb : d74857 q = 1) : d81499 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d70120, d81499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8737 q ha hb
    | true =>
      simp only [d70120, d81499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70121 q = 1) (hb : d74857 q = 1) : d81500 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d70121, d81500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70121, d81500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70122 q = 1) (hb : d74857 q = 1) : d81501 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d70122, d81501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70122, d81501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70123 q = 1) (hb : d74857 q = 1) : d81502 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d70123, d81502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70123, d81502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70124 q = 1) (hb : d74857 q = 1) : d81503 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d70124, d81503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70124, d81503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70125 q = 1) (hb : d74857 q = 1) : d81504 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d70125, d81504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70125, d81504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8739 (p : Pattern) (ha : d70131 p = 1) (hb : d74857 p = 1) : d81510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70126 q = 1) (hb : d74857 q = 1) : d81505 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d70126, d81505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8738 q ha hb
    | true =>
      simp only [d70126, d81505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70127 q = 1) (hb : d74857 q = 1) : d81506 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d70127, d81506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70127, d81506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70128 q = 1) (hb : d74857 q = 1) : d81507 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d70128, d81507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70128, d81507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70129 q = 1) (hb : d74857 q = 1) : d81508 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d70129, d81508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70129, d81508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70130 q = 1) (hb : d74857 q = 1) : d81509 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d70130, d81509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70130, d81509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70131 q = 1) (hb : d74857 q = 1) : d81510 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d70131, d81510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70131, d81510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8740 (p : Pattern) (ha : d70137 p = 1) (hb : d74857 p = 1) : d81516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70132 q = 1) (hb : d74857 q = 1) : d81511 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d70132, d81511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8739 q ha hb
    | true =>
      simp only [d70132, d81511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70133 q = 1) (hb : d74857 q = 1) : d81512 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d70133, d81512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70133, d81512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70134 q = 1) (hb : d74857 q = 1) : d81513 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d70134, d81513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70134, d81513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70135 q = 1) (hb : d74857 q = 1) : d81514 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d70135, d81514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70135, d81514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70136 q = 1) (hb : d74857 q = 1) : d81515 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d70136, d81515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70136, d81515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70137 q = 1) (hb : d74857 q = 1) : d81516 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d70137, d81516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70137, d81516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8741 (p : Pattern) (ha : d70143 p = 1) (hb : d74857 p = 1) : d81522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70138 q = 1) (hb : d74857 q = 1) : d81517 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d70138, d81517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8740 q ha hb
    | true =>
      simp only [d70138, d81517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70139 q = 1) (hb : d74857 q = 1) : d81518 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d70139, d81518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70139, d81518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70140 q = 1) (hb : d74857 q = 1) : d81519 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d70140, d81519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70140, d81519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70141 q = 1) (hb : d74857 q = 1) : d81520 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d70141, d81520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70141, d81520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70142 q = 1) (hb : d74857 q = 1) : d81521 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d70142, d81521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70142, d81521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70143 q = 1) (hb : d74857 q = 1) : d81522 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d70143, d81522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70143, d81522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8742 (p : Pattern) (ha : d81398 p = 1) (hb : d81522 p = 1) : d81522 p = 1 := by
  have h0 (q : Pattern) (ha : d81398 q = 1) (hb : d81522 q = 1) : d81522 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro8743 (p : Pattern) (ha : d69967 p = 1) (hb : d74857 p = 1) : d69967 p = 1 := by
  have h0 (q : Pattern) (ha : d69967 q = 1) (hb : d74857 q = 1) : d69967 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro8744 (p : Pattern) (ha : d104 p = 1) (hb : d81127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d102 q = 1) (hb : d81125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d81125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, d81125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d103 q = 1) (hb : d81126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d81126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d81126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d104 q = 1) (hb : d81127 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d81127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d81127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8745 (p : Pattern) (ha : d111 p = 1) (hb : d81130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d102 q = 1) (hb : d81125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d81125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, d81125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d103 q = 1) (hb : d81126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d81126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d81126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d107 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h11 (q : Pattern) (ha : d109 q = 1) (hb : d81128 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d81128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d81128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d110 q = 1) (hb : d81129 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d81129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d81129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d111 q = 1) (hb : d81130 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d81130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d111, d81130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro8746 (p : Pattern) (ha : d406 p = 1) (hb : d81135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d109 q = 1) (hb : d81128 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d81128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d81128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d110 q = 1) (hb : d81129 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d81129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d81129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d406 q = 1) (hb : d81135 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d81135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d81135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8747 (p : Pattern) (ha : d462 p = 1) (hb : d81143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d459 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d460 q = 1) (hb : d81141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d81141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d81141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d461 q = 1) (hb : d81142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d81142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d81142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d462 q = 1) (hb : d81143 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d81143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d81143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8748 (p : Pattern) (ha : d53647 p = 1) (hb : d81149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d81131 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d81131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8744 q ha hb
    | true =>
      simp only [d112, d81131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8745 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d81132 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d81132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d81132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d81133 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d81133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, d81133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d81134 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d81134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d81134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d81136 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d81136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, d81136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8746 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d81137 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d81137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, d81137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d81138 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d81138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, d81138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d81139 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d81139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, d81139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d81140 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d81140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, d81140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d81144 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d81144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, d81144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8747 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d81145 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d81145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, d81145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d81146 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d81146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, d81146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d81147 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d81147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, d81147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d81148 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d81148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, d81148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d81149 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d81149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53647, d81149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8749 (p : Pattern) (ha : d4693 p = 1) (hb : d81157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52138 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d370 q = 1) (hb : d52138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4689 q = 1) (hb : d52138 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4690 q = 1) (hb : d52138 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d4691 q = 1) (hb : d81155 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4691, d81155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4691, d81155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4692 q = 1) (hb : d81156 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4692, d81156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4692, d81156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4693 q = 1) (hb : d81157 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4693, d81157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4693, d81157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
end NetHack.Soko22Hazard87
