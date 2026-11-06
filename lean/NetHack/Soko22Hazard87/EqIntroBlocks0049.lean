import NetHack.Soko22Hazard87.EqIntroBlocks0048
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro12250 (p : Pattern) (selected : d12224 p = 2) : d109322 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12219 q = 2) : d109317 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d12219, d109317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12249 q selected
    | true =>
      simp only [d12219, d109317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12220 q = 2) : d109318 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d12220, d109318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12220, d109318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12221 q = 2) : d109319 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d12221, d109319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12221, d109319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12222 q = 2) : d109320 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d12222, d109320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12222, d109320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12223 q = 2) : d109321 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d12223, d109321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12223, d109321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12224 q = 2) : d109322 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d12224, d109322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12224, d109322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12251 (p : Pattern) (selected : d139756 p = 0) : d140070 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d77915 q = 0) : d78864 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77915, d78864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3901 q selected
    | true =>
      simp only [d77915, d78864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d77916 q = 0) : d78865 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77916, d78865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d77916, d78865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d77917 q = 0) : d78866 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77917, d78866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d77917, d78866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d77918 q = 0) : d78867 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77918, d78867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d77918, d78867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d77922 q = 0) : d78871 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77922, d78871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3902 q selected
    | true =>
      simp only [d77922, d78871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d77923 q = 0) : d78872 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77923, d78872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d77923, d78872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d77924 q = 0) : d78873 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77924, d78873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d77924, d78873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d77931 q = 0) : d78880 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77931, d78880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3904 q selected
    | true =>
      simp only [d77931, d78880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3890 q selected
  have h9 (q : Pattern) (selected : d77938 q = 0) : d78801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77938, d78801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3906 q selected
    | true =>
      simp only [d77938, d78801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d77939 q = 0) : d78881 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77939, d78881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d77939, d78881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d139753 q = 0) : d140067 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139753, d140067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139753, d140067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d139754 q = 0) : d140068 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139754, d140068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d139754, d140068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d139755 q = 0) : d140069 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139755, d140069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139755, d140069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d139756 q = 0) : d140070 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139756, d140070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139756, d140070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro12252 (p : Pattern) (selected : d139760 p = 0) : d140074 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d77915 q = 0) : d78864 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77915, d78864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3901 q selected
    | true =>
      simp only [d77915, d78864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d77916 q = 0) : d78865 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77916, d78865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d77916, d78865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d77917 q = 0) : d78866 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77917, d78866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d77917, d78866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d77918 q = 0) : d78867 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77918, d78867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d77918, d78867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d77922 q = 0) : d78871 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77922, d78871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3902 q selected
    | true =>
      simp only [d77922, d78871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d77923 q = 0) : d78872 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77923, d78872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d77923, d78872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d77924 q = 0) : d78873 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77924, d78873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d77924, d78873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d77931 q = 0) : d78880 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77931, d78880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3904 q selected
    | true =>
      simp only [d77931, d78880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3890 q selected
  have h9 (q : Pattern) (selected : d77938 q = 0) : d78801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77938, d78801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3906 q selected
    | true =>
      simp only [d77938, d78801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d77939 q = 0) : d78881 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77939, d78881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d77939, d78881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d139753 q = 0) : d140067 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139753, d140067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139753, d140067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d139754 q = 0) : d140068 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139754, d140068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d139754, d140068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d139755 q = 0) : d140069 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139755, d140069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139755, d140069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d77945 q = 0) : d78887 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77945, d78887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3908 q selected
    | true =>
      simp only [d77945, d78887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d77946 q = 0) : d78888 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77946, d78888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d77946, d78888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d77947 q = 0) : d78889 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77947, d78889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d77947, d78889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d77948 q = 0) : d78890 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77948, d78890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d77948, d78890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d77950 q = 0) : d78892 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77950, d78892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3909 q selected
    | true =>
      simp only [d77950, d78892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d77951 q = 0) : d78893 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77951, d78893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d77951, d78893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d77952 q = 0) : d78894 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77952, d78894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d77952, d78894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d77954 q = 0) : d78896 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77954, d78896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3910 q selected
    | true =>
      simp only [d77954, d78896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3892 q selected
  have h22 (q : Pattern) (selected : d77956 q = 0) : d78808 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77956, d78808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3911 q selected
    | true =>
      simp only [d77956, d78808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d77957 q = 0) : d78897 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77957, d78897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d77957, d78897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  have h24 (q : Pattern) (selected : d139757 q = 0) : d140071 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139757, d140071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d139757, d140071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d139758 q = 0) : d140072 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139758, d140072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d139758, d140072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d139759 q = 0) : d140073 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139759, d140073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d139759, d140073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d139760 q = 0) : d140074 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139760, d140074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139760, d140074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro12253 (p : Pattern) (selected : d139767 p = 0) : d140081 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d77954 q = 0) : d78896 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77954, d78896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3910 q selected
    | true =>
      simp only [d77954, d78896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3892 q selected
  have h2 (q : Pattern) (selected : d77956 q = 0) : d78808 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77956, d78808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3911 q selected
    | true =>
      simp only [d77956, d78808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d77957 q = 0) : d78897 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77957, d78897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d77957, d78897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139757 q = 0) : d140071 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139757, d140071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139757, d140071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139765 q = 0) : d140079 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139765, d140079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139765, d140079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139766 q = 0) : d140080 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139766, d140080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139766, d140080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139767 q = 0) : d140081 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139767, d140081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139767, d140081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12254 (p : Pattern) (selected : d139776 p = 0) : d140090 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d77982 q = 0) : d78922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77982, d78922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3916 q selected
    | true =>
      simp only [d77982, d78922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3896 q selected
  have h2 (q : Pattern) (selected : d77989 q = 0) : d78830 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77989, d78830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3918 q selected
    | true =>
      simp only [d77989, d78830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d77990 q = 0) : d78923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77990, d78923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d77990, d78923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139773 q = 0) : d140087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139773, d140087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139773, d140087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139774 q = 0) : d140088 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139774, d140088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139774, d140088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139775 q = 0) : d140089 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139775, d140089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139775, d140089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139776 q = 0) : d140090 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139776, d140090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139776, d140090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12255 (p : Pattern) (selected : d139782 p = 0) : d140096 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d77903 q = 0) : d78852 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77903, d78852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d77903, d78852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3899 q selected
  have h2 (q : Pattern) (selected : d77904 q = 0) : d78853 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77904, d78853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d77904, d78853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d77910 q = 0) : d78859 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77910, d78859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3899 q selected
    | true =>
      simp only [d77910, d78859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3900 q selected
  have h4 (q : Pattern) (selected : d77911 q = 0) : d78860 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77911, d78860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d77911, d78860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d77912 q = 0) : d78861 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77912, d78861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d77912, d78861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139761 q = 0) : d140075 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139761, d140075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12251 q selected
    | true =>
      simp only [d139761, d140075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12252 q selected
  have h7 (q : Pattern) (selected : d77964 q = 0) : d78904 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77964, d78904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3913 q selected
    | true =>
      simp only [d77964, d78904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d139762 q = 0) : d140076 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139762, d140076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d139762, d140076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d139763 q = 0) : d140077 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139763, d140077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139763, d140077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d139764 q = 0) : d140078 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139764, d140078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139764, d140078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d139768 q = 0) : d140082 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139768, d140082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139768, d140082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12253 q selected
  have h12 (q : Pattern) (selected : d139769 q = 0) : d140083 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139769, d140083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d139769, d140083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d139770 q = 0) : d140084 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139770, d140084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d139770, d140084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d139771 q = 0) : d140085 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139771, d140085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139771, d140085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d139772 q = 0) : d140086 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139772, d140086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139772, d140086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d139777 q = 0) : d140091 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139777, d140091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139777, d140091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12254 q selected
  have h17 (q : Pattern) (selected : d139778 q = 0) : d140092 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139778, d140092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d139778, d140092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d139779 q = 0) : d140093 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139779, d140093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d139779, d140093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d139780 q = 0) : d140094 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139780, d140094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d139780, d140094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d139781 q = 0) : d140095 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139781, d140095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d139781, d140095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d139782 q = 0) : d140096 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d139782, d140096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d139782, d140096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro12256 (p : Pattern) (selected : d139788 p = 0) : d140102 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d77893 q = 0) : d78842 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77893, d78842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d77893, d78842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3898 q selected
  have h2 (q : Pattern) (selected : d77894 q = 0) : d78843 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77894, d78843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d77894, d78843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d77895 q = 0) : d78844 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77895, d78844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d77895, d78844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d77896 q = 0) : d78845 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77896, d78845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d77896, d78845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d77897 q = 0) : d78846 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77897, d78846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d77897, d78846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139783 q = 0) : d140097 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d139783, d140097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139783, d140097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12255 q selected
  have h7 (q : Pattern) (selected : d139784 q = 0) : d140098 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d139784, d140098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139784, d140098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d139785 q = 0) : d140099 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d139785, d140099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139785, d140099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d139786 q = 0) : d140100 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d139786, d140100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139786, d140100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d139787 q = 0) : d140101 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d139787, d140101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139787, d140101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d139788 q = 0) : d140102 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d139788, d140102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139788, d140102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro12257 (p : Pattern) (selected : d139794 p = 0) : d140108 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78033 q = 0) : d78966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78033, d78966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3927 q selected
    | true =>
      simp only [d78033, d78966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78034 q = 0) : d78967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78034, d78967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78034, d78967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78035 q = 0) : d78968 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78035, d78968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78035, d78968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78036 q = 0) : d78969 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78036, d78969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78036, d78969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d78040 q = 0) : d78973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78040, d78973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3928 q selected
    | true =>
      simp only [d78040, d78973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d78041 q = 0) : d78974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78041, d78974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78041, d78974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d78042 q = 0) : d78975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78042, d78975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d78042, d78975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d139789 q = 0) : d140103 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139789, d140103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3930 q selected
    | true =>
      simp only [d139789, d140103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3923 q selected
  have h9 (q : Pattern) (selected : d78062 q = 0) : d78946 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78062, d78946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3934 q selected
    | true =>
      simp only [d78062, d78946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d139790 q = 0) : d140104 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139790, d140104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139790, d140104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d139791 q = 0) : d140105 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139791, d140105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139791, d140105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d139792 q = 0) : d140106 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139792, d140106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d139792, d140106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d139793 q = 0) : d140107 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139793, d140107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139793, d140107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d139794 q = 0) : d140108 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139794, d140108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139794, d140108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro12258 (p : Pattern) (selected : d139800 p = 0) : d140114 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78033 q = 0) : d78966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78033, d78966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3927 q selected
    | true =>
      simp only [d78033, d78966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78034 q = 0) : d78967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78034, d78967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78034, d78967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78035 q = 0) : d78968 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78035, d78968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78035, d78968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78036 q = 0) : d78969 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78036, d78969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78036, d78969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d78040 q = 0) : d78973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78040, d78973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3928 q selected
    | true =>
      simp only [d78040, d78973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d78041 q = 0) : d78974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78041, d78974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78041, d78974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d78042 q = 0) : d78975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78042, d78975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d78042, d78975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d139789 q = 0) : d140103 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139789, d140103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3930 q selected
    | true =>
      simp only [d139789, d140103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3923 q selected
  have h9 (q : Pattern) (selected : d78062 q = 0) : d78946 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78062, d78946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3934 q selected
    | true =>
      simp only [d78062, d78946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d139790 q = 0) : d140104 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139790, d140104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139790, d140104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d139791 q = 0) : d140105 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139791, d140105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139791, d140105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d139792 q = 0) : d140106 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139792, d140106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d139792, d140106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d139793 q = 0) : d140107 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139793, d140107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139793, d140107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d78070 q = 0) : d78996 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78070, d78996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3936 q selected
    | true =>
      simp only [d78070, d78996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d78071 q = 0) : d78997 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78071, d78997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78071, d78997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d78072 q = 0) : d78998 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78072, d78998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d78072, d78998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d78073 q = 0) : d78999 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78073, d78999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78073, d78999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d78075 q = 0) : d79001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78075, d79001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3937 q selected
    | true =>
      simp only [d78075, d79001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d78076 q = 0) : d79002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78076, d79002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78076, d79002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d78077 q = 0) : d79003 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78077, d79003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d78077, d79003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d139795 q = 0) : d140109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139795, d140109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3938 q selected
    | true =>
      simp only [d139795, d140109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3925 q selected
  have h22 (q : Pattern) (selected : d78082 q = 0) : d78955 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78082, d78955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3940 q selected
    | true =>
      simp only [d78082, d78955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d139796 q = 0) : d140110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139796, d140110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d139796, d140110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  have h24 (q : Pattern) (selected : d139797 q = 0) : d140111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139797, d140111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d139797, d140111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d139798 q = 0) : d140112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139798, d140112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d139798, d140112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d139799 q = 0) : d140113 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139799, d140113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d139799, d140113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d139800 q = 0) : d140114 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139800, d140114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139800, d140114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro12259 (p : Pattern) (selected : d139802 p = 0) : d140116 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78013 q = 0) : d78946 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78013, d78946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3923 q selected
    | true =>
      simp only [d78013, d78946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78014 q = 0) : d78947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78014, d78947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78014, d78947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78015 q = 0) : d78948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78015, d78948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78015, d78948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78016 q = 0) : d78949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78016, d78949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78016, d78949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d78017 q = 0) : d78950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78017, d78950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78017, d78950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139802 q = 0) : d140116 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139802, d140116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139802, d140116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12260 (p : Pattern) (selected : d139809 p = 0) : d140123 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d139795 q = 0) : d140109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139795, d140109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3938 q selected
    | true =>
      simp only [d139795, d140109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3925 q selected
  have h2 (q : Pattern) (selected : d78082 q = 0) : d78955 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78082, d78955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3940 q selected
    | true =>
      simp only [d78082, d78955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139796 q = 0) : d140110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139796, d140110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139796, d140110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139797 q = 0) : d140111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139797, d140111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139797, d140111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139807 q = 0) : d140121 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139807, d140121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139807, d140121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139808 q = 0) : d140122 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139808, d140122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139808, d140122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139809 q = 0) : d140123 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139809, d140123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139809, d140123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12261 (p : Pattern) (selected : d139820 p = 0) : d140134 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d139815 q = 0) : d140129 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139815, d140129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3945 q selected
    | true =>
      simp only [d139815, d140129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3951 q selected
  have h2 (q : Pattern) (selected : d78127 q = 0) : d79051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78127, d79051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3949 q selected
    | true =>
      simp only [d78127, d79051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139816 q = 0) : d140130 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139816, d140130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139816, d140130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139817 q = 0) : d140131 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139817, d140131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139817, d140131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139818 q = 0) : d140132 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139818, d140132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139818, d140132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139819 q = 0) : d140133 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139819, d140133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139819, d140133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139820 q = 0) : d140134 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139820, d140134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139820, d140134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12262 (p : Pattern) (selected : d139826 p = 0) : d140140 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78019 q = 0) : d78952 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78019, d78952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78019, d78952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3924 q selected
  have h2 (q : Pattern) (selected : d78020 q = 0) : d78953 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78020, d78953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d78020, d78953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d78028 q = 0) : d78961 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78028, d78961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3924 q selected
    | true =>
      simp only [d78028, d78961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3926 q selected
  have h4 (q : Pattern) (selected : d78029 q = 0) : d78962 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78029, d78962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d78029, d78962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d78030 q = 0) : d78963 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78030, d78963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78030, d78963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139801 q = 0) : d140115 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139801, d140115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12257 q selected
    | true =>
      simp only [d139801, d140115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12258 q selected
  have h7 (q : Pattern) (selected : d139803 q = 0) : d140117 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139803, d140117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12259 q selected
    | true =>
      simp only [d139803, d140117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d139804 q = 0) : d140118 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139804, d140118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d139804, d140118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d139805 q = 0) : d140119 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139805, d140119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139805, d140119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d139806 q = 0) : d140120 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139806, d140120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139806, d140120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d139810 q = 0) : d140124 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139810, d140124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139810, d140124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12260 q selected
  have h12 (q : Pattern) (selected : d139811 q = 0) : d140125 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139811, d140125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d139811, d140125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d139812 q = 0) : d140126 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139812, d140126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d139812, d140126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d139813 q = 0) : d140127 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139813, d140127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139813, d140127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d139814 q = 0) : d140128 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139814, d140128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139814, d140128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d139821 q = 0) : d140135 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139821, d140135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139821, d140135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12261 q selected
  have h17 (q : Pattern) (selected : d139822 q = 0) : d140136 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139822, d140136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d139822, d140136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d139823 q = 0) : d140137 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139823, d140137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d139823, d140137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d139824 q = 0) : d140138 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139824, d140138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d139824, d140138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d139825 q = 0) : d140139 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139825, d140139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d139825, d140139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d139826 q = 0) : d140140 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d139826, d140140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d139826, d140140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro12263 (p : Pattern) (selected : d139832 p = 0) : d140146 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d139827 q = 0) : d140141 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d139827, d140141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139827, d140141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12262 q selected
  have h2 (q : Pattern) (selected : d139828 q = 0) : d140142 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d139828, d140142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139828, d140142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d139829 q = 0) : d140143 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d139829, d140143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139829, d140143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139830 q = 0) : d140144 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d139830, d140144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139830, d140144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d139831 q = 0) : d140145 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d139831, d140145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139831, d140145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139832 q = 0) : d140146 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d139832, d140146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139832, d140146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12264 (p : Pattern) (selected : d139839 p = 0) : d140153 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78180 q = 0) : d79097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78180, d79097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3960 q selected
    | true =>
      simp only [d78180, d79097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78181 q = 0) : d79098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78181, d79098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78181, d79098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78182 q = 0) : d79099 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78182, d79099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78182, d79099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78183 q = 0) : d79100 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78183, d79100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78183, d79100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d78187 q = 0) : d79104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78187, d79104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3961 q selected
    | true =>
      simp only [d78187, d79104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d78188 q = 0) : d79105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78188, d79105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78188, d79105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d78189 q = 0) : d79106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78189, d79106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d78189, d79106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d139834 q = 0) : d140148 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139834, d140148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3963 q selected
    | true =>
      simp only [d139834, d140148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3956 q selected
  have h9 (q : Pattern) (selected : d78209 q = 0) : d79077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78209, d79077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3967 q selected
    | true =>
      simp only [d78209, d79077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d139835 q = 0) : d140149 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139835, d140149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139835, d140149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d139836 q = 0) : d140150 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139836, d140150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139836, d140150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d139837 q = 0) : d140151 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139837, d140151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d139837, d140151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d139838 q = 0) : d140152 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139838, d140152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139838, d140152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d139839 q = 0) : d140153 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139839, d140153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139839, d140153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro12265 (p : Pattern) (selected : d139845 p = 0) : d140159 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78180 q = 0) : d79097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78180, d79097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3960 q selected
    | true =>
      simp only [d78180, d79097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78181 q = 0) : d79098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78181, d79098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78181, d79098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78182 q = 0) : d79099 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78182, d79099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78182, d79099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78183 q = 0) : d79100 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78183, d79100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78183, d79100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d78187 q = 0) : d79104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78187, d79104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3961 q selected
    | true =>
      simp only [d78187, d79104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d78188 q = 0) : d79105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78188, d79105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78188, d79105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d78189 q = 0) : d79106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78189, d79106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d78189, d79106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d139834 q = 0) : d140148 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139834, d140148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3963 q selected
    | true =>
      simp only [d139834, d140148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3956 q selected
  have h9 (q : Pattern) (selected : d78209 q = 0) : d79077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78209, d79077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3967 q selected
    | true =>
      simp only [d78209, d79077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d139835 q = 0) : d140149 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139835, d140149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139835, d140149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d139836 q = 0) : d140150 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139836, d140150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139836, d140150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d139837 q = 0) : d140151 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139837, d140151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d139837, d140151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d139838 q = 0) : d140152 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139838, d140152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139838, d140152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d78217 q = 0) : d79127 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78217, d79127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3969 q selected
    | true =>
      simp only [d78217, d79127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d78218 q = 0) : d79128 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78218, d79128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78218, d79128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d78219 q = 0) : d79129 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78219, d79129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d78219, d79129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d78220 q = 0) : d79130 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78220, d79130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78220, d79130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d78222 q = 0) : d79132 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78222, d79132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3970 q selected
    | true =>
      simp only [d78222, d79132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d78223 q = 0) : d79133 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78223, d79133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78223, d79133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d78224 q = 0) : d79134 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78224, d79134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d78224, d79134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d139840 q = 0) : d140154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139840, d140154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3971 q selected
    | true =>
      simp only [d139840, d140154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3958 q selected
  have h22 (q : Pattern) (selected : d78229 q = 0) : d79086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78229, d79086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3973 q selected
    | true =>
      simp only [d78229, d79086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d139841 q = 0) : d140155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139841, d140155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d139841, d140155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  have h24 (q : Pattern) (selected : d139842 q = 0) : d140156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139842, d140156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d139842, d140156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d139843 q = 0) : d140157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139843, d140157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d139843, d140157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d139844 q = 0) : d140158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139844, d140158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d139844, d140158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d139845 q = 0) : d140159 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139845, d140159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139845, d140159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro12266 (p : Pattern) (selected : d139847 p = 0) : d140161 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78160 q = 0) : d79077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78160, d79077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3956 q selected
    | true =>
      simp only [d78160, d79077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78161 q = 0) : d79078 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78161, d79078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78161, d79078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78162 q = 0) : d79079 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78162, d79079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78162, d79079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78163 q = 0) : d79080 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78163, d79080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78163, d79080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d78164 q = 0) : d79081 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78164, d79081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78164, d79081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139847 q = 0) : d140161 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139847, d140161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139847, d140161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12267 (p : Pattern) (selected : d139854 p = 0) : d140168 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d139840 q = 0) : d140154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139840, d140154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3971 q selected
    | true =>
      simp only [d139840, d140154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3958 q selected
  have h2 (q : Pattern) (selected : d78229 q = 0) : d79086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78229, d79086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3973 q selected
    | true =>
      simp only [d78229, d79086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139841 q = 0) : d140155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139841, d140155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139841, d140155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139842 q = 0) : d140156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139842, d140156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139842, d140156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139852 q = 0) : d140166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139852, d140166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139852, d140166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139853 q = 0) : d140167 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139853, d140167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139853, d140167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139854 q = 0) : d140168 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139854, d140168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139854, d140168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12268 (p : Pattern) (selected : d139865 p = 0) : d140179 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d139860 q = 0) : d140174 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139860, d140174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3978 q selected
    | true =>
      simp only [d139860, d140174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3984 q selected
  have h2 (q : Pattern) (selected : d78274 q = 0) : d79182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78274, d79182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3982 q selected
    | true =>
      simp only [d78274, d79182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139861 q = 0) : d140175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139861, d140175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139861, d140175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139862 q = 0) : d140176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139862, d140176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139862, d140176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139863 q = 0) : d140177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139863, d140177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139863, d140177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139864 q = 0) : d140178 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139864, d140178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139864, d140178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139865 q = 0) : d140179 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139865, d140179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139865, d140179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12269 (p : Pattern) (selected : d139871 p = 0) : d140185 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78166 q = 0) : d79083 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78166, d79083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78166, d79083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3957 q selected
  have h2 (q : Pattern) (selected : d78167 q = 0) : d79084 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78167, d79084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d78167, d79084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d78175 q = 0) : d79092 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78175, d79092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3957 q selected
    | true =>
      simp only [d78175, d79092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3959 q selected
  have h4 (q : Pattern) (selected : d78176 q = 0) : d79093 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78176, d79093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d78176, d79093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d78177 q = 0) : d79094 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78177, d79094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78177, d79094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139846 q = 0) : d140160 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139846, d140160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12264 q selected
    | true =>
      simp only [d139846, d140160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12265 q selected
  have h7 (q : Pattern) (selected : d139848 q = 0) : d140162 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139848, d140162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12266 q selected
    | true =>
      simp only [d139848, d140162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d139849 q = 0) : d140163 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139849, d140163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d139849, d140163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d139850 q = 0) : d140164 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139850, d140164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139850, d140164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d139851 q = 0) : d140165 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139851, d140165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139851, d140165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d139855 q = 0) : d140169 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139855, d140169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139855, d140169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12267 q selected
  have h12 (q : Pattern) (selected : d139856 q = 0) : d140170 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139856, d140170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d139856, d140170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d139857 q = 0) : d140171 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139857, d140171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d139857, d140171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d139858 q = 0) : d140172 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139858, d140172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139858, d140172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d139859 q = 0) : d140173 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139859, d140173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139859, d140173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d139866 q = 0) : d140180 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139866, d140180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139866, d140180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12268 q selected
  have h17 (q : Pattern) (selected : d139867 q = 0) : d140181 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139867, d140181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d139867, d140181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d139868 q = 0) : d140182 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139868, d140182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d139868, d140182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d139869 q = 0) : d140183 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139869, d140183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d139869, d140183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d139870 q = 0) : d140184 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139870, d140184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d139870, d140184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d139871 q = 0) : d140185 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d139871, d140185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d139871, d140185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro12270 (p : Pattern) (selected : d139877 p = 0) : d140191 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d139872 q = 0) : d140186 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d139872, d140186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139872, d140186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12269 q selected
  have h2 (q : Pattern) (selected : d139873 q = 0) : d140187 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d139873, d140187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139873, d140187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d139874 q = 0) : d140188 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d139874, d140188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139874, d140188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139875 q = 0) : d140189 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d139875, d140189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139875, d140189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d139876 q = 0) : d140190 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d139876, d140190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139876, d140190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139877 q = 0) : d140191 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d139877, d140191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139877, d140191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12271 (p : Pattern) (selected : d139885 p = 0) : d140199 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78328 q = 0) : d79229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78328, d79229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3993 q selected
    | true =>
      simp only [d78328, d79229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78329 q = 0) : d79230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78329, d79230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78329, d79230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78330 q = 0) : d79231 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78330, d79231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78330, d79231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78331 q = 0) : d79232 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78331, d79232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78331, d79232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d78335 q = 0) : d79236 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78335, d79236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3994 q selected
    | true =>
      simp only [d78335, d79236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d78336 q = 0) : d79237 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78336, d79237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78336, d79237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d78337 q = 0) : d79238 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78337, d79238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d78337, d79238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d139880 q = 0) : d140194 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139880, d140194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3996 q selected
    | true =>
      simp only [d139880, d140194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3989 q selected
  have h9 (q : Pattern) (selected : d78357 q = 0) : d79209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78357, d79209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4000 q selected
    | true =>
      simp only [d78357, d79209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d139881 q = 0) : d140195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139881, d140195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139881, d140195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d139882 q = 0) : d140196 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139882, d140196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139882, d140196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d139883 q = 0) : d140197 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139883, d140197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d139883, d140197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d139884 q = 0) : d140198 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139884, d140198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139884, d140198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d139885 q = 0) : d140199 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139885, d140199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139885, d140199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro12272 (p : Pattern) (selected : d139891 p = 0) : d140205 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78328 q = 0) : d79229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78328, d79229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3993 q selected
    | true =>
      simp only [d78328, d79229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78329 q = 0) : d79230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78329, d79230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78329, d79230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78330 q = 0) : d79231 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78330, d79231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78330, d79231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78331 q = 0) : d79232 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78331, d79232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78331, d79232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d78335 q = 0) : d79236 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78335, d79236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3994 q selected
    | true =>
      simp only [d78335, d79236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d78336 q = 0) : d79237 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78336, d79237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78336, d79237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d78337 q = 0) : d79238 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78337, d79238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d78337, d79238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d139880 q = 0) : d140194 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139880, d140194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3996 q selected
    | true =>
      simp only [d139880, d140194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3989 q selected
  have h9 (q : Pattern) (selected : d78357 q = 0) : d79209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78357, d79209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4000 q selected
    | true =>
      simp only [d78357, d79209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d139881 q = 0) : d140195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139881, d140195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139881, d140195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d139882 q = 0) : d140196 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139882, d140196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139882, d140196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d139883 q = 0) : d140197 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139883, d140197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d139883, d140197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d139884 q = 0) : d140198 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139884, d140198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139884, d140198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d78365 q = 0) : d79259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78365, d79259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4002 q selected
    | true =>
      simp only [d78365, d79259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d78366 q = 0) : d79260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78366, d79260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78366, d79260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d78367 q = 0) : d79261 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78367, d79261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d78367, d79261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d78368 q = 0) : d79262 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78368, d79262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78368, d79262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d78370 q = 0) : d79264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78370, d79264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4003 q selected
    | true =>
      simp only [d78370, d79264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d78371 q = 0) : d79265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78371, d79265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78371, d79265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d78372 q = 0) : d79266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78372, d79266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d78372, d79266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d139886 q = 0) : d140200 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139886, d140200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4004 q selected
    | true =>
      simp only [d139886, d140200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3991 q selected
  have h22 (q : Pattern) (selected : d78377 q = 0) : d79218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78377, d79218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4006 q selected
    | true =>
      simp only [d78377, d79218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d139887 q = 0) : d140201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139887, d140201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d139887, d140201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  have h24 (q : Pattern) (selected : d139888 q = 0) : d140202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139888, d140202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d139888, d140202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d139889 q = 0) : d140203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139889, d140203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d139889, d140203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d139890 q = 0) : d140204 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139890, d140204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d139890, d140204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d139891 q = 0) : d140205 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139891, d140205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139891, d140205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro12273 (p : Pattern) (selected : d139893 p = 0) : d140207 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78308 q = 0) : d79209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78308, d79209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3989 q selected
    | true =>
      simp only [d78308, d79209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78309 q = 0) : d79210 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78309, d79210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78309, d79210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78310 q = 0) : d79211 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78310, d79211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78310, d79211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78311 q = 0) : d79212 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78311, d79212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78311, d79212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d78312 q = 0) : d79213 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78312, d79213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78312, d79213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139893 q = 0) : d140207 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139893, d140207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139893, d140207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12274 (p : Pattern) (selected : d139900 p = 0) : d140214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d139886 q = 0) : d140200 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139886, d140200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4004 q selected
    | true =>
      simp only [d139886, d140200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3991 q selected
  have h2 (q : Pattern) (selected : d78377 q = 0) : d79218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78377, d79218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4006 q selected
    | true =>
      simp only [d78377, d79218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139887 q = 0) : d140201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139887, d140201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139887, d140201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139888 q = 0) : d140202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139888, d140202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139888, d140202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139898 q = 0) : d140212 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139898, d140212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139898, d140212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139899 q = 0) : d140213 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139899, d140213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139899, d140213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139900 q = 0) : d140214 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139900, d140214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139900, d140214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12275 (p : Pattern) (selected : d139911 p = 0) : d140225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d139906 q = 0) : d140220 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139906, d140220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4011 q selected
    | true =>
      simp only [d139906, d140220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4017 q selected
  have h2 (q : Pattern) (selected : d78422 q = 0) : d79314 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78422, d79314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4015 q selected
    | true =>
      simp only [d78422, d79314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139907 q = 0) : d140221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139907, d140221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139907, d140221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139908 q = 0) : d140222 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139908, d140222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139908, d140222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139909 q = 0) : d140223 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139909, d140223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139909, d140223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139910 q = 0) : d140224 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139910, d140224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139910, d140224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139911 q = 0) : d140225 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139911, d140225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139911, d140225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12276 (p : Pattern) (selected : d139917 p = 0) : d140231 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78314 q = 0) : d79215 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78314, d79215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78314, d79215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3990 q selected
  have h2 (q : Pattern) (selected : d78315 q = 0) : d79216 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78315, d79216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d78315, d79216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d78323 q = 0) : d79224 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78323, d79224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3990 q selected
    | true =>
      simp only [d78323, d79224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3992 q selected
  have h4 (q : Pattern) (selected : d78324 q = 0) : d79225 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78324, d79225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d78324, d79225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d78325 q = 0) : d79226 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78325, d79226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78325, d79226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139892 q = 0) : d140206 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139892, d140206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12271 q selected
    | true =>
      simp only [d139892, d140206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12272 q selected
  have h7 (q : Pattern) (selected : d139894 q = 0) : d140208 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139894, d140208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12273 q selected
    | true =>
      simp only [d139894, d140208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d139895 q = 0) : d140209 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139895, d140209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d139895, d140209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d139896 q = 0) : d140210 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139896, d140210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139896, d140210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d139897 q = 0) : d140211 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139897, d140211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139897, d140211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d139901 q = 0) : d140215 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139901, d140215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139901, d140215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12274 q selected
  have h12 (q : Pattern) (selected : d139902 q = 0) : d140216 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139902, d140216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d139902, d140216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d139903 q = 0) : d140217 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139903, d140217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d139903, d140217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d139904 q = 0) : d140218 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139904, d140218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139904, d140218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d139905 q = 0) : d140219 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139905, d140219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139905, d140219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d139912 q = 0) : d140226 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139912, d140226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139912, d140226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12275 q selected
  have h17 (q : Pattern) (selected : d139913 q = 0) : d140227 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139913, d140227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d139913, d140227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d139914 q = 0) : d140228 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139914, d140228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d139914, d140228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d139915 q = 0) : d140229 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139915, d140229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d139915, d140229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d139916 q = 0) : d140230 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139916, d140230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d139916, d140230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d139917 q = 0) : d140231 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d139917, d140231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d139917, d140231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro12277 (p : Pattern) (selected : d139923 p = 0) : d140237 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d139918 q = 0) : d140232 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d139918, d140232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139918, d140232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12276 q selected
  have h2 (q : Pattern) (selected : d139919 q = 0) : d140233 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d139919, d140233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139919, d140233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d139920 q = 0) : d140234 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d139920, d140234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139920, d140234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139921 q = 0) : d140235 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d139921, d140235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139921, d140235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d139922 q = 0) : d140236 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d139922, d140236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139922, d140236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139923 q = 0) : d140237 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d139923, d140237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139923, d140237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12278 (p : Pattern) (selected : d139932 p = 0) : d140246 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78477 q = 0) : d79362 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78477, d79362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4026 q selected
    | true =>
      simp only [d78477, d79362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78478 q = 0) : d79363 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78478, d79363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78478, d79363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78479 q = 0) : d79364 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78479, d79364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78479, d79364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78480 q = 0) : d79365 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78480, d79365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78480, d79365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d78484 q = 0) : d79369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78484, d79369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4027 q selected
    | true =>
      simp only [d78484, d79369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d78485 q = 0) : d79370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78485, d79370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78485, d79370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d78486 q = 0) : d79371 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78486, d79371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d78486, d79371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d139927 q = 0) : d140241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139927, d140241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4029 q selected
    | true =>
      simp only [d139927, d140241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4022 q selected
  have h9 (q : Pattern) (selected : d78506 q = 0) : d79342 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78506, d79342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4033 q selected
    | true =>
      simp only [d78506, d79342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d139928 q = 0) : d140242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139928, d140242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139928, d140242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d139929 q = 0) : d140243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139929, d140243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139929, d140243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d139930 q = 0) : d140244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139930, d140244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d139930, d140244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d139931 q = 0) : d140245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139931, d140245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139931, d140245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d139932 q = 0) : d140246 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139932, d140246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139932, d140246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro12279 (p : Pattern) (selected : d139938 p = 0) : d140252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78477 q = 0) : d79362 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78477, d79362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4026 q selected
    | true =>
      simp only [d78477, d79362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78478 q = 0) : d79363 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78478, d79363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78478, d79363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78479 q = 0) : d79364 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78479, d79364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78479, d79364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78480 q = 0) : d79365 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78480, d79365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78480, d79365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d78484 q = 0) : d79369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78484, d79369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4027 q selected
    | true =>
      simp only [d78484, d79369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d78485 q = 0) : d79370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78485, d79370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78485, d79370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d78486 q = 0) : d79371 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78486, d79371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d78486, d79371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d139927 q = 0) : d140241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139927, d140241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4029 q selected
    | true =>
      simp only [d139927, d140241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4022 q selected
  have h9 (q : Pattern) (selected : d78506 q = 0) : d79342 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78506, d79342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4033 q selected
    | true =>
      simp only [d78506, d79342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d139928 q = 0) : d140242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139928, d140242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139928, d140242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d139929 q = 0) : d140243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139929, d140243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139929, d140243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d139930 q = 0) : d140244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139930, d140244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d139930, d140244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d139931 q = 0) : d140245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139931, d140245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139931, d140245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d78514 q = 0) : d79392 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78514, d79392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4035 q selected
    | true =>
      simp only [d78514, d79392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d78515 q = 0) : d79393 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78515, d79393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78515, d79393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d78516 q = 0) : d79394 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78516, d79394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d78516, d79394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d78517 q = 0) : d79395 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78517, d79395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78517, d79395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d78519 q = 0) : d79397 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78519, d79397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4036 q selected
    | true =>
      simp only [d78519, d79397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d78520 q = 0) : d79398 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78520, d79398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78520, d79398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d78521 q = 0) : d79399 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78521, d79399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d78521, d79399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d139933 q = 0) : d140247 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139933, d140247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4037 q selected
    | true =>
      simp only [d139933, d140247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4024 q selected
  have h22 (q : Pattern) (selected : d78526 q = 0) : d79351 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78526, d79351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4039 q selected
    | true =>
      simp only [d78526, d79351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d139934 q = 0) : d140248 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139934, d140248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d139934, d140248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  have h24 (q : Pattern) (selected : d139935 q = 0) : d140249 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139935, d140249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d139935, d140249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d139936 q = 0) : d140250 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139936, d140250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d139936, d140250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d139937 q = 0) : d140251 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139937, d140251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d139937, d140251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d139938 q = 0) : d140252 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139938, d140252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139938, d140252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro12280 (p : Pattern) (selected : d139940 p = 0) : d140254 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78457 q = 0) : d79342 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78457, d79342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4022 q selected
    | true =>
      simp only [d78457, d79342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78458 q = 0) : d79343 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78458, d79343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78458, d79343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78459 q = 0) : d79344 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78459, d79344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78459, d79344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78460 q = 0) : d79345 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78460, d79345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78460, d79345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d78461 q = 0) : d79346 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78461, d79346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78461, d79346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139940 q = 0) : d140254 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139940, d140254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139940, d140254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12281 (p : Pattern) (selected : d139947 p = 0) : d140261 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d139933 q = 0) : d140247 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139933, d140247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4037 q selected
    | true =>
      simp only [d139933, d140247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4024 q selected
  have h2 (q : Pattern) (selected : d78526 q = 0) : d79351 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78526, d79351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4039 q selected
    | true =>
      simp only [d78526, d79351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139934 q = 0) : d140248 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139934, d140248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139934, d140248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139935 q = 0) : d140249 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139935, d140249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139935, d140249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139945 q = 0) : d140259 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139945, d140259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139945, d140259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139946 q = 0) : d140260 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139946, d140260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139946, d140260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139947 q = 0) : d140261 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139947, d140261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139947, d140261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12282 (p : Pattern) (selected : d139958 p = 0) : d140272 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d139953 q = 0) : d140267 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139953, d140267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4044 q selected
    | true =>
      simp only [d139953, d140267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4050 q selected
  have h2 (q : Pattern) (selected : d78571 q = 0) : d79447 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78571, d79447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4048 q selected
    | true =>
      simp only [d78571, d79447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139954 q = 0) : d140268 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139954, d140268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139954, d140268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139955 q = 0) : d140269 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139955, d140269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139955, d140269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139956 q = 0) : d140270 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139956, d140270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139956, d140270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139957 q = 0) : d140271 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139957, d140271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139957, d140271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139958 q = 0) : d140272 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139958, d140272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139958, d140272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12283 (p : Pattern) (selected : d139964 p = 0) : d140278 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78463 q = 0) : d79348 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78463, d79348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78463, d79348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4023 q selected
  have h2 (q : Pattern) (selected : d78464 q = 0) : d79349 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78464, d79349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d78464, d79349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d78472 q = 0) : d79357 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78472, d79357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4023 q selected
    | true =>
      simp only [d78472, d79357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4025 q selected
  have h4 (q : Pattern) (selected : d78473 q = 0) : d79358 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78473, d79358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d78473, d79358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d78474 q = 0) : d79359 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78474, d79359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78474, d79359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139939 q = 0) : d140253 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139939, d140253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12278 q selected
    | true =>
      simp only [d139939, d140253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12279 q selected
  have h7 (q : Pattern) (selected : d139941 q = 0) : d140255 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139941, d140255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12280 q selected
    | true =>
      simp only [d139941, d140255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d139942 q = 0) : d140256 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139942, d140256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d139942, d140256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d139943 q = 0) : d140257 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139943, d140257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139943, d140257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d139944 q = 0) : d140258 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139944, d140258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139944, d140258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d139948 q = 0) : d140262 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139948, d140262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139948, d140262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12281 q selected
  have h12 (q : Pattern) (selected : d139949 q = 0) : d140263 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139949, d140263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d139949, d140263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d139950 q = 0) : d140264 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139950, d140264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d139950, d140264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d139951 q = 0) : d140265 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139951, d140265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139951, d140265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d139952 q = 0) : d140266 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139952, d140266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139952, d140266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d139959 q = 0) : d140273 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139959, d140273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139959, d140273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12282 q selected
  have h17 (q : Pattern) (selected : d139960 q = 0) : d140274 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139960, d140274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d139960, d140274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d139961 q = 0) : d140275 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139961, d140275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d139961, d140275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d139962 q = 0) : d140276 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139962, d140276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d139962, d140276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d139963 q = 0) : d140277 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139963, d140277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d139963, d140277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d139964 q = 0) : d140278 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d139964, d140278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d139964, d140278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro12284 (p : Pattern) (selected : d139970 p = 0) : d140284 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d139965 q = 0) : d140279 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d139965, d140279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139965, d140279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12283 q selected
  have h2 (q : Pattern) (selected : d139966 q = 0) : d140280 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d139966, d140280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139966, d140280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d139967 q = 0) : d140281 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d139967, d140281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139967, d140281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139968 q = 0) : d140282 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d139968, d140282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139968, d140282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d139969 q = 0) : d140283 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d139969, d140283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139969, d140283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139970 q = 0) : d140284 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d139970, d140284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139970, d140284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12285 (p : Pattern) (selected : d139980 p = 0) : d140294 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78627 q = 0) : d79496 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78627, d79496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4059 q selected
    | true =>
      simp only [d78627, d79496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78628 q = 0) : d79497 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78628, d79497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78628, d79497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78629 q = 0) : d79498 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78629, d79498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78629, d79498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78630 q = 0) : d79499 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78630, d79499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78630, d79499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d78634 q = 0) : d79503 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78634, d79503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4060 q selected
    | true =>
      simp only [d78634, d79503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d78635 q = 0) : d79504 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78635, d79504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78635, d79504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d78636 q = 0) : d79505 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78636, d79505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d78636, d79505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d139975 q = 0) : d140289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139975, d140289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4062 q selected
    | true =>
      simp only [d139975, d140289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4055 q selected
  have h9 (q : Pattern) (selected : d78656 q = 0) : d79476 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78656, d79476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4066 q selected
    | true =>
      simp only [d78656, d79476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d139976 q = 0) : d140290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139976, d140290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139976, d140290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d139977 q = 0) : d140291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139977, d140291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139977, d140291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d139978 q = 0) : d140292 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139978, d140292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d139978, d140292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d139979 q = 0) : d140293 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139979, d140293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139979, d140293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d139980 q = 0) : d140294 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139980, d140294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139980, d140294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro12286 (p : Pattern) (selected : d139986 p = 0) : d140300 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78627 q = 0) : d79496 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78627, d79496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4059 q selected
    | true =>
      simp only [d78627, d79496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78628 q = 0) : d79497 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78628, d79497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78628, d79497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78629 q = 0) : d79498 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78629, d79498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78629, d79498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78630 q = 0) : d79499 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78630, d79499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78630, d79499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d78634 q = 0) : d79503 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78634, d79503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4060 q selected
    | true =>
      simp only [d78634, d79503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d78635 q = 0) : d79504 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78635, d79504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78635, d79504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d78636 q = 0) : d79505 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78636, d79505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d78636, d79505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d139975 q = 0) : d140289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139975, d140289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4062 q selected
    | true =>
      simp only [d139975, d140289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4055 q selected
  have h9 (q : Pattern) (selected : d78656 q = 0) : d79476 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78656, d79476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4066 q selected
    | true =>
      simp only [d78656, d79476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d139976 q = 0) : d140290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139976, d140290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139976, d140290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d139977 q = 0) : d140291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139977, d140291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139977, d140291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d139978 q = 0) : d140292 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139978, d140292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d139978, d140292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d139979 q = 0) : d140293 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139979, d140293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139979, d140293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d78664 q = 0) : d79526 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78664, d79526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4068 q selected
    | true =>
      simp only [d78664, d79526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d78665 q = 0) : d79527 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78665, d79527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78665, d79527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d78666 q = 0) : d79528 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78666, d79528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d78666, d79528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d78667 q = 0) : d79529 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78667, d79529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78667, d79529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d78669 q = 0) : d79531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78669, d79531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4069 q selected
    | true =>
      simp only [d78669, d79531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d78670 q = 0) : d79532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78670, d79532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78670, d79532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d78671 q = 0) : d79533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78671, d79533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d78671, d79533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d139981 q = 0) : d140295 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139981, d140295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4070 q selected
    | true =>
      simp only [d139981, d140295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4057 q selected
  have h22 (q : Pattern) (selected : d78676 q = 0) : d79485 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78676, d79485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4072 q selected
    | true =>
      simp only [d78676, d79485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d139982 q = 0) : d140296 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139982, d140296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d139982, d140296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  have h24 (q : Pattern) (selected : d139983 q = 0) : d140297 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139983, d140297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d139983, d140297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d139984 q = 0) : d140298 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139984, d140298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d139984, d140298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d139985 q = 0) : d140299 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139985, d140299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d139985, d140299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d139986 q = 0) : d140300 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139986, d140300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139986, d140300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro12287 (p : Pattern) (selected : d139988 p = 0) : d140302 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78607 q = 0) : d79476 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78607, d79476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4055 q selected
    | true =>
      simp only [d78607, d79476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78608 q = 0) : d79477 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78608, d79477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78608, d79477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78609 q = 0) : d79478 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78609, d79478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78609, d79478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78610 q = 0) : d79479 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78610, d79479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78610, d79479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d78611 q = 0) : d79480 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78611, d79480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78611, d79480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139988 q = 0) : d140302 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139988, d140302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139988, d140302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12288 (p : Pattern) (selected : d139995 p = 0) : d140309 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d139981 q = 0) : d140295 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d139981, d140295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4070 q selected
    | true =>
      simp only [d139981, d140295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4057 q selected
  have h2 (q : Pattern) (selected : d78676 q = 0) : d79485 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78676, d79485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4072 q selected
    | true =>
      simp only [d78676, d79485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139982 q = 0) : d140296 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139982, d140296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139982, d140296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139983 q = 0) : d140297 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139983, d140297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139983, d140297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139993 q = 0) : d140307 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139993, d140307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139993, d140307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139994 q = 0) : d140308 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139994, d140308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139994, d140308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139995 q = 0) : d140309 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139995, d140309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139995, d140309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12289 (p : Pattern) (selected : d140006 p = 0) : d140320 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d140001 q = 0) : d140315 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140001, d140315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4077 q selected
    | true =>
      simp only [d140001, d140315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4083 q selected
  have h2 (q : Pattern) (selected : d78721 q = 0) : d79581 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78721, d79581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4081 q selected
    | true =>
      simp only [d78721, d79581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d140002 q = 0) : d140316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140002, d140316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140002, d140316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d140003 q = 0) : d140317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140003, d140317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d140003, d140317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d140004 q = 0) : d140318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140004, d140318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d140004, d140318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d140005 q = 0) : d140319 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140005, d140319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d140005, d140319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d140006 q = 0) : d140320 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140006, d140320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d140006, d140320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12290 (p : Pattern) (selected : d140012 p = 0) : d140326 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78613 q = 0) : d79482 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78613, d79482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78613, d79482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4056 q selected
  have h2 (q : Pattern) (selected : d78614 q = 0) : d79483 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78614, d79483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d78614, d79483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d78622 q = 0) : d79491 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78622, d79491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4056 q selected
    | true =>
      simp only [d78622, d79491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4058 q selected
  have h4 (q : Pattern) (selected : d78623 q = 0) : d79492 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78623, d79492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d78623, d79492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d78624 q = 0) : d79493 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78624, d79493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d78624, d79493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139987 q = 0) : d140301 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139987, d140301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12285 q selected
    | true =>
      simp only [d139987, d140301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12286 q selected
  have h7 (q : Pattern) (selected : d139989 q = 0) : d140303 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139989, d140303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12287 q selected
    | true =>
      simp only [d139989, d140303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d139990 q = 0) : d140304 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139990, d140304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d139990, d140304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d139991 q = 0) : d140305 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139991, d140305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139991, d140305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d139992 q = 0) : d140306 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139992, d140306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139992, d140306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d139996 q = 0) : d140310 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139996, d140310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139996, d140310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12288 q selected
  have h12 (q : Pattern) (selected : d139997 q = 0) : d140311 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139997, d140311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d139997, d140311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d139998 q = 0) : d140312 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139998, d140312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d139998, d140312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d139999 q = 0) : d140313 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139999, d140313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139999, d140313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d140000 q = 0) : d140314 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d140000, d140314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d140000, d140314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d140007 q = 0) : d140321 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140007, d140321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d140007, d140321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12289 q selected
  have h17 (q : Pattern) (selected : d140008 q = 0) : d140322 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d140008, d140322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d140008, d140322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d140009 q = 0) : d140323 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d140009, d140323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d140009, d140323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d140010 q = 0) : d140324 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d140010, d140324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d140010, d140324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d140011 q = 0) : d140325 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d140011, d140325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d140011, d140325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d140012 q = 0) : d140326 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d140012, d140326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d140012, d140326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro12291 (p : Pattern) (selected : d140018 p = 0) : d140332 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d140013 q = 0) : d140327 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d140013, d140327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d140013, d140327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12290 q selected
  have h2 (q : Pattern) (selected : d140014 q = 0) : d140328 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d140014, d140328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d140014, d140328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d140015 q = 0) : d140329 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d140015, d140329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d140015, d140329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d140016 q = 0) : d140330 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d140016, d140330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d140016, d140330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d140017 q = 0) : d140331 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d140017, d140331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d140017, d140331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d140018 q = 0) : d140332 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d140018, d140332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d140018, d140332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12292 (p : Pattern) (selected : d140024 p = 0) : d140338 p = 1 := by
  have h0 (q : Pattern) (selected : d139833 q = 0) : d140147 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d139833, d140147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12256 q selected
    | true =>
      simp only [d139833, d140147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12263 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d139878 q = 0) : d140192 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d139878, d140192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139878, d140192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12270 q selected
  have h3 (q : Pattern) (selected : d139879 q = 0) : d140193 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d139879, d140193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139879, d140193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139924 q = 0) : d140238 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d139924, d140238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139924, d140238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12277 q selected
  have h5 (q : Pattern) (selected : d139925 q = 0) : d140239 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d139925, d140239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139925, d140239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139926 q = 0) : d140240 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d139926, d140240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139926, d140240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139971 q = 0) : d140285 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d139971, d140285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139971, d140285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12284 q selected
  have h8 (q : Pattern) (selected : d139972 q = 0) : d140286 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d139972, d140286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139972, d140286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d139973 q = 0) : d140287 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d139973, d140287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139973, d140287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d139974 q = 0) : d140288 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d139974, d140288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d139974, d140288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d140019 q = 0) : d140333 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d140019, d140333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140019, d140333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12291 q selected
  have h12 (q : Pattern) (selected : d140020 q = 0) : d140334 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d140020, d140334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140020, d140334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d140021 q = 0) : d140335 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d140021, d140335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140021, d140335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d140022 q = 0) : d140336 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d140022, d140336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140022, d140336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d140023 q = 0) : d140337 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d140023, d140337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d140023, d140337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d140024 q = 0) : d140338 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d140024, d140338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d140024, d140338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro12293 (p : Pattern) (selected : d140030 p = 0) : d140344 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d140025 q = 0) : d140339 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d140025, d140339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12292 q selected
    | true =>
      simp only [d140025, d140339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d140026 q = 0) : d140340 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d140026, d140340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140026, d140340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d140027 q = 0) : d140341 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d140027, d140341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d140027, d140341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d140028 q = 0) : d140342 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d140028, d140342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d140028, d140342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d140029 q = 0) : d140343 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d140029, d140343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d140029, d140343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d140030 q = 0) : d140344 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d140030, d140344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d140030, d140344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12294 (p : Pattern) (selected : d140036 p = 0) : d140350 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d140031 q = 0) : d140345 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d140031, d140345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12293 q selected
    | true =>
      simp only [d140031, d140345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d140032 q = 0) : d140346 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d140032, d140346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140032, d140346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d140033 q = 0) : d140347 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d140033, d140347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d140033, d140347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d140034 q = 0) : d140348 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d140034, d140348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d140034, d140348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d140035 q = 0) : d140349 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d140035, d140349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d140035, d140349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d140036 q = 0) : d140350 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d140036, d140350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d140036, d140350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12295 (p : Pattern) (selected : d140042 p = 0) : d140356 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d140037 q = 0) : d140351 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d140037, d140351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12294 q selected
    | true =>
      simp only [d140037, d140351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d140038 q = 0) : d140352 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d140038, d140352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140038, d140352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d140039 q = 0) : d140353 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d140039, d140353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d140039, d140353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d140040 q = 0) : d140354 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d140040, d140354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d140040, d140354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d140041 q = 0) : d140355 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d140041, d140355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d140041, d140355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d140042 q = 0) : d140356 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d140042, d140356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d140042, d140356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12296 (p : Pattern) (selected : d140048 p = 0) : d140362 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d140043 q = 0) : d140357 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d140043, d140357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12295 q selected
    | true =>
      simp only [d140043, d140357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d140044 q = 0) : d140358 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d140044, d140358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140044, d140358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d140045 q = 0) : d140359 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d140045, d140359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d140045, d140359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d140046 q = 0) : d140360 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d140046, d140360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d140046, d140360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d140047 q = 0) : d140361 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d140047, d140361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d140047, d140361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d140048 q = 0) : d140362 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d140048, d140362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d140048, d140362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12297 (p : Pattern) (selected : d140054 p = 0) : d140368 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d140049 q = 0) : d140363 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d140049, d140363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12296 q selected
    | true =>
      simp only [d140049, d140363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d140050 q = 0) : d140364 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d140050, d140364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140050, d140364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d140051 q = 0) : d140365 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d140051, d140365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d140051, d140365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d140052 q = 0) : d140366 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d140052, d140366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d140052, d140366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d140053 q = 0) : d140367 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d140053, d140367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d140053, d140367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d140054 q = 0) : d140368 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d140054, d140368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d140054, d140368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12298 (p : Pattern) (selected : d140060 p = 0) : d140374 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d140055 q = 0) : d140369 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d140055, d140369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12297 q selected
    | true =>
      simp only [d140055, d140369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d140056 q = 0) : d140370 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d140056, d140370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140056, d140370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d140057 q = 0) : d140371 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d140057, d140371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d140057, d140371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d140058 q = 0) : d140372 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d140058, d140372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d140058, d140372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d140059 q = 0) : d140373 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d140059, d140373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d140059, d140373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d140060 q = 0) : d140374 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d140060, d140374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d140060, d140374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12299 (p : Pattern) (selected : d140066 p = 0) : d140380 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d140061 q = 0) : d140375 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d140061, d140375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12298 q selected
    | true =>
      simp only [d140061, d140375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d140062 q = 0) : d140376 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d140062, d140376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140062, d140376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d140063 q = 0) : d140377 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d140063, d140377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d140063, d140377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d140064 q = 0) : d140378 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d140064, d140378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d140064, d140378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d140065 q = 0) : d140379 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d140065, d140379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d140065, d140379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d140066 q = 0) : d140380 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d140066, d140380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d140066, d140380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12300 (p : Pattern) (selected : d139756 p = 1) : d141016 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d77918 q = 1) : d77918 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d77924 q = 1) : d77924 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d77931 q = 1) : d77931 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d77938 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4096 q selected
    | true =>
      simp only [d77938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d77939 q = 1) : d80559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77939, d80559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d77939, d80559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139753 q = 1) : d141013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139753, d141013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139753, d141013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d139754 q = 1) : d141014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139754, d141014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d139754, d141014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d139755 q = 1) : d141015 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139755, d141015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139755, d141015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d139756 q = 1) : d141016 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139756, d141016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139756, d141016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro12301 (p : Pattern) (selected : d139760 p = 1) : d141020 p = 1 := by
  have h0 (q : Pattern) (selected : d77918 q = 1) : d77918 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d77924 q = 1) : d77924 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d77931 q = 1) : d77931 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d77938 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4096 q selected
    | true =>
      simp only [d77938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d77939 q = 1) : d80559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77939, d80559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d77939, d80559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139753 q = 1) : d141013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139753, d141013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139753, d141013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h7 (q : Pattern) (selected : d139754 q = 1) : d141014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139754, d141014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139754, d141014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d139755 q = 1) : d141015 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139755, d141015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139755, d141015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d77948 q = 1) : d77948 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d77952 q = 1) : d77952 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d77954 q = 1) : d77954 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d77956 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4098 q selected
    | true =>
      simp only [d77956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h13 (q : Pattern) (selected : d77957 q = 1) : d80564 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77957, d80564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d77957, d80564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d139757 q = 1) : d141017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139757, d141017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139757, d141017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h15 (q : Pattern) (selected : d139758 q = 1) : d141018 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139758, d141018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139758, d141018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d139759 q = 1) : d141019 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139759, d141019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d139759, d141019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d139760 q = 1) : d141020 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139760, d141020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139760, d141020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro12302 (p : Pattern) (selected : d139767 p = 1) : d141027 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d77954 q = 1) : d77954 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d77956 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4098 q selected
    | true =>
      simp only [d77956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d77957 q = 1) : d80564 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77957, d80564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d77957, d80564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139757 q = 1) : d141017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139757, d141017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139757, d141017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139765 q = 1) : d141025 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139765, d141025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139765, d141025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139766 q = 1) : d141026 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139766, d141026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139766, d141026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139767 q = 1) : d141027 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139767, d141027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139767, d141027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12303 (p : Pattern) (selected : d139776 p = 1) : d141036 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d77982 q = 1) : d77982 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d77989 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4102 q selected
    | true =>
      simp only [d77989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d77990 q = 1) : d80581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77990, d80581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d77990, d80581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139773 q = 1) : d141033 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139773, d141033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139773, d141033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139774 q = 1) : d141034 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139774, d141034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139774, d141034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139775 q = 1) : d141035 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139775, d141035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139775, d141035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139776 q = 1) : d141036 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139776, d141036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139776, d141036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12304 (p : Pattern) (selected : d139782 p = 1) : d141042 p = 1 := by
  have h0 (q : Pattern) (selected : d77912 q = 1) : d77912 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d139761 q = 1) : d141021 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139761, d141021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12300 q selected
    | true =>
      simp only [d139761, d141021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12301 q selected
  have h2 (q : Pattern) (selected : d77964 q = 1) : d77964 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d139762 q = 1) : d141022 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139762, d141022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139762, d141022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d139763 q = 1) : d141023 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139763, d141023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139763, d141023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139764 q = 1) : d141024 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139764, d141024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139764, d141024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139768 q = 1) : d141028 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139768, d141028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139768, d141028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12302 q selected
  have h8 (q : Pattern) (selected : d139769 q = 1) : d141029 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139769, d141029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d139769, d141029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d139770 q = 1) : d141030 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139770, d141030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139770, d141030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d139771 q = 1) : d141031 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139771, d141031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d139771, d141031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d139772 q = 1) : d141032 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139772, d141032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d139772, d141032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d139777 q = 1) : d141037 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139777, d141037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139777, d141037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12303 q selected
  have h13 (q : Pattern) (selected : d139778 q = 1) : d141038 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139778, d141038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d139778, d141038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d139779 q = 1) : d141039 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139779, d141039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139779, d141039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d139780 q = 1) : d141040 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139780, d141040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d139780, d141040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d139781 q = 1) : d141041 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139781, d141041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d139781, d141041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d139782 q = 1) : d141042 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d139782, d141042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d139782, d141042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro12305 (p : Pattern) (selected : d139788 p = 1) : d141048 p = 1 := by
  have h0 (q : Pattern) (selected : d77897 q = 1) : d77897 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d139783 q = 1) : d141043 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d139783, d141043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139783, d141043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12304 q selected
  have h3 (q : Pattern) (selected : d139784 q = 1) : d141044 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d139784, d141044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139784, d141044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139785 q = 1) : d141045 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d139785, d141045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139785, d141045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d139786 q = 1) : d141046 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d139786, d141046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139786, d141046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139787 q = 1) : d141047 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d139787, d141047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139787, d141047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139788 q = 1) : d141048 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d139788, d141048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139788, d141048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12306 (p : Pattern) (selected : d139794 p = 1) : d141053 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78036 q = 1) : d78036 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d78042 q = 1) : d78042 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d139789 q = 1) : d139789 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d78062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4107 q selected
    | true =>
      simp only [d78062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139790 q = 1) : d141049 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139790, d141049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139790, d141049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139791 q = 1) : d141050 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139791, d141050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139791, d141050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d139792 q = 1) : d141051 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139792, d141051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d139792, d141051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d139793 q = 1) : d141052 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139793, d141052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139793, d141052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d139794 q = 1) : d141053 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139794, d141053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139794, d141053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro12307 (p : Pattern) (selected : d139800 p = 1) : d141058 p = 1 := by
  have h0 (q : Pattern) (selected : d78036 q = 1) : d78036 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78042 q = 1) : d78042 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d139789 q = 1) : d139789 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d78062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4107 q selected
    | true =>
      simp only [d78062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d139790 q = 1) : d141049 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139790, d141049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d139790, d141049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139791 q = 1) : d141050 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139791, d141050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139791, d141050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h7 (q : Pattern) (selected : d139792 q = 1) : d141051 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139792, d141051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139792, d141051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d139793 q = 1) : d141052 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139793, d141052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139793, d141052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d78073 q = 1) : d78073 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d78077 q = 1) : d78077 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d139795 q = 1) : d139795 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d78082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4109 q selected
    | true =>
      simp only [d78082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h13 (q : Pattern) (selected : d139796 q = 1) : d141054 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139796, d141054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d139796, d141054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d139797 q = 1) : d141055 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139797, d141055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139797, d141055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h15 (q : Pattern) (selected : d139798 q = 1) : d141056 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139798, d141056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139798, d141056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d139799 q = 1) : d141057 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139799, d141057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d139799, d141057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d139800 q = 1) : d141058 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139800, d141058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139800, d141058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro12308 (p : Pattern) (selected : d139809 p = 1) : d141065 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d139795 q = 1) : d139795 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d78082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4109 q selected
    | true =>
      simp only [d78082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139796 q = 1) : d141054 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139796, d141054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139796, d141054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139797 q = 1) : d141055 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139797, d141055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139797, d141055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139807 q = 1) : d141063 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139807, d141063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139807, d141063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139808 q = 1) : d141064 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139808, d141064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139808, d141064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139809 q = 1) : d141065 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139809, d141065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139809, d141065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12309 (p : Pattern) (selected : d139820 p = 1) : d141075 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d139815 q = 1) : d139815 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d78127 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4113 q selected
    | true =>
      simp only [d78127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139816 q = 1) : d141071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139816, d141071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139816, d141071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139817 q = 1) : d141072 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139817, d141072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139817, d141072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139818 q = 1) : d141073 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139818, d141073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139818, d141073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139819 q = 1) : d141074 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139819, d141074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139819, d141074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139820 q = 1) : d141075 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139820, d141075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139820, d141075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12310 (p : Pattern) (selected : d139826 p = 1) : d141081 p = 1 := by
  have h0 (q : Pattern) (selected : d78030 q = 1) : d78030 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d139801 q = 1) : d141059 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139801, d141059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12306 q selected
    | true =>
      simp only [d139801, d141059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12307 q selected
  have h2 (q : Pattern) (selected : d139803 q = 1) : d139803 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d139804 q = 1) : d141060 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139804, d141060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139804, d141060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d139805 q = 1) : d141061 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139805, d141061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139805, d141061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139806 q = 1) : d141062 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139806, d141062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139806, d141062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139810 q = 1) : d141066 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139810, d141066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139810, d141066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12308 q selected
  have h8 (q : Pattern) (selected : d139811 q = 1) : d141067 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139811, d141067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d139811, d141067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d139812 q = 1) : d141068 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139812, d141068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139812, d141068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d139813 q = 1) : d141069 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139813, d141069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d139813, d141069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d139814 q = 1) : d141070 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139814, d141070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d139814, d141070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d139821 q = 1) : d141076 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139821, d141076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139821, d141076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12309 q selected
  have h13 (q : Pattern) (selected : d139822 q = 1) : d141077 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139822, d141077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d139822, d141077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d139823 q = 1) : d141078 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139823, d141078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139823, d141078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d139824 q = 1) : d141079 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139824, d141079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d139824, d141079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d139825 q = 1) : d141080 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139825, d141080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d139825, d141080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d139826 q = 1) : d141081 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d139826, d141081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d139826, d141081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro12311 (p : Pattern) (selected : d139832 p = 1) : d141087 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d139827 q = 1) : d141082 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d139827, d141082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139827, d141082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12310 q selected
  have h2 (q : Pattern) (selected : d139828 q = 1) : d141083 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d139828, d141083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139828, d141083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d139829 q = 1) : d141084 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d139829, d141084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139829, d141084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139830 q = 1) : d141085 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d139830, d141085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139830, d141085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d139831 q = 1) : d141086 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d139831, d141086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139831, d141086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139832 q = 1) : d141087 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d139832, d141087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139832, d141087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12312 (p : Pattern) (selected : d139839 p = 1) : d141093 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78183 q = 1) : d78183 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d78189 q = 1) : d78189 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d139834 q = 1) : d139834 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d78209 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4118 q selected
    | true =>
      simp only [d78209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139835 q = 1) : d141089 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139835, d141089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139835, d141089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139836 q = 1) : d141090 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139836, d141090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139836, d141090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d139837 q = 1) : d141091 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139837, d141091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d139837, d141091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d139838 q = 1) : d141092 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139838, d141092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139838, d141092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d139839 q = 1) : d141093 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139839, d141093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139839, d141093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro12313 (p : Pattern) (selected : d139845 p = 1) : d141098 p = 1 := by
  have h0 (q : Pattern) (selected : d78183 q = 1) : d78183 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78189 q = 1) : d78189 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d139834 q = 1) : d139834 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d78209 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4118 q selected
    | true =>
      simp only [d78209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d139835 q = 1) : d141089 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139835, d141089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d139835, d141089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139836 q = 1) : d141090 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139836, d141090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139836, d141090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h7 (q : Pattern) (selected : d139837 q = 1) : d141091 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139837, d141091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139837, d141091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d139838 q = 1) : d141092 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139838, d141092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139838, d141092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d78220 q = 1) : d78220 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d78224 q = 1) : d78224 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d139840 q = 1) : d139840 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d78229 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4120 q selected
    | true =>
      simp only [d78229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h13 (q : Pattern) (selected : d139841 q = 1) : d141094 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139841, d141094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d139841, d141094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d139842 q = 1) : d141095 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139842, d141095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139842, d141095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h15 (q : Pattern) (selected : d139843 q = 1) : d141096 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139843, d141096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139843, d141096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d139844 q = 1) : d141097 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139844, d141097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d139844, d141097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d139845 q = 1) : d141098 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139845, d141098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139845, d141098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro12314 (p : Pattern) (selected : d139854 p = 1) : d141105 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d139840 q = 1) : d139840 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d78229 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4120 q selected
    | true =>
      simp only [d78229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139841 q = 1) : d141094 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139841, d141094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139841, d141094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139842 q = 1) : d141095 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139842, d141095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139842, d141095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139852 q = 1) : d141103 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139852, d141103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139852, d141103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139853 q = 1) : d141104 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139853, d141104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139853, d141104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139854 q = 1) : d141105 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139854, d141105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139854, d141105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12315 (p : Pattern) (selected : d139865 p = 1) : d141115 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d139860 q = 1) : d139860 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d78274 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4124 q selected
    | true =>
      simp only [d78274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139861 q = 1) : d141111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139861, d141111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139861, d141111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139862 q = 1) : d141112 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139862, d141112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139862, d141112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139863 q = 1) : d141113 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139863, d141113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139863, d141113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139864 q = 1) : d141114 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139864, d141114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139864, d141114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139865 q = 1) : d141115 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139865, d141115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139865, d141115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12316 (p : Pattern) (selected : d139871 p = 1) : d141121 p = 1 := by
  have h0 (q : Pattern) (selected : d78177 q = 1) : d78177 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d139846 q = 1) : d141099 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139846, d141099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12312 q selected
    | true =>
      simp only [d139846, d141099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12313 q selected
  have h2 (q : Pattern) (selected : d139848 q = 1) : d139848 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d139849 q = 1) : d141100 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139849, d141100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139849, d141100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d139850 q = 1) : d141101 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139850, d141101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139850, d141101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139851 q = 1) : d141102 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139851, d141102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139851, d141102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139855 q = 1) : d141106 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139855, d141106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139855, d141106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12314 q selected
  have h8 (q : Pattern) (selected : d139856 q = 1) : d141107 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139856, d141107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d139856, d141107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d139857 q = 1) : d141108 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139857, d141108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139857, d141108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d139858 q = 1) : d141109 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139858, d141109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d139858, d141109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d139859 q = 1) : d141110 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139859, d141110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d139859, d141110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d139866 q = 1) : d141116 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139866, d141116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139866, d141116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12315 q selected
  have h13 (q : Pattern) (selected : d139867 q = 1) : d141117 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139867, d141117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d139867, d141117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d139868 q = 1) : d141118 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139868, d141118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139868, d141118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d139869 q = 1) : d141119 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139869, d141119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d139869, d141119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d139870 q = 1) : d141120 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139870, d141120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d139870, d141120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d139871 q = 1) : d141121 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d139871, d141121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d139871, d141121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro12317 (p : Pattern) (selected : d139877 p = 1) : d141127 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d139872 q = 1) : d141122 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d139872, d141122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139872, d141122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12316 q selected
  have h2 (q : Pattern) (selected : d139873 q = 1) : d141123 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d139873, d141123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139873, d141123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d139874 q = 1) : d141124 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d139874, d141124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139874, d141124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139875 q = 1) : d141125 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d139875, d141125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139875, d141125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d139876 q = 1) : d141126 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d139876, d141126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139876, d141126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139877 q = 1) : d141127 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d139877, d141127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139877, d141127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12318 (p : Pattern) (selected : d139885 p = 1) : d141134 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78331 q = 1) : d78331 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d78337 q = 1) : d78337 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d139880 q = 1) : d139880 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d78357 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4129 q selected
    | true =>
      simp only [d78357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139881 q = 1) : d141130 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139881, d141130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139881, d141130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139882 q = 1) : d141131 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139882, d141131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139882, d141131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d139883 q = 1) : d141132 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139883, d141132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d139883, d141132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d139884 q = 1) : d141133 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139884, d141133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139884, d141133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d139885 q = 1) : d141134 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139885, d141134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139885, d141134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro12319 (p : Pattern) (selected : d139891 p = 1) : d141139 p = 1 := by
  have h0 (q : Pattern) (selected : d78331 q = 1) : d78331 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78337 q = 1) : d78337 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d139880 q = 1) : d139880 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d78357 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4129 q selected
    | true =>
      simp only [d78357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d139881 q = 1) : d141130 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139881, d141130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d139881, d141130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139882 q = 1) : d141131 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139882, d141131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139882, d141131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h7 (q : Pattern) (selected : d139883 q = 1) : d141132 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139883, d141132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139883, d141132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d139884 q = 1) : d141133 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139884, d141133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139884, d141133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d78368 q = 1) : d78368 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d78372 q = 1) : d78372 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d139886 q = 1) : d139886 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d78377 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4131 q selected
    | true =>
      simp only [d78377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h13 (q : Pattern) (selected : d139887 q = 1) : d141135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139887, d141135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d139887, d141135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d139888 q = 1) : d141136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139888, d141136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139888, d141136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h15 (q : Pattern) (selected : d139889 q = 1) : d141137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139889, d141137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139889, d141137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d139890 q = 1) : d141138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139890, d141138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d139890, d141138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d139891 q = 1) : d141139 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139891, d141139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139891, d141139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro12320 (p : Pattern) (selected : d139900 p = 1) : d141146 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d139886 q = 1) : d139886 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d78377 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4131 q selected
    | true =>
      simp only [d78377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139887 q = 1) : d141135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139887, d141135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139887, d141135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139888 q = 1) : d141136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139888, d141136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139888, d141136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139898 q = 1) : d141144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139898, d141144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139898, d141144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139899 q = 1) : d141145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139899, d141145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139899, d141145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139900 q = 1) : d141146 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139900, d141146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139900, d141146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12321 (p : Pattern) (selected : d139911 p = 1) : d141156 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d139906 q = 1) : d139906 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d78422 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4135 q selected
    | true =>
      simp only [d78422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139907 q = 1) : d141152 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139907, d141152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139907, d141152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139908 q = 1) : d141153 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139908, d141153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139908, d141153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139909 q = 1) : d141154 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139909, d141154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139909, d141154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139910 q = 1) : d141155 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139910, d141155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139910, d141155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139911 q = 1) : d141156 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139911, d141156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139911, d141156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12322 (p : Pattern) (selected : d139917 p = 1) : d141162 p = 1 := by
  have h0 (q : Pattern) (selected : d78325 q = 1) : d78325 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d139892 q = 1) : d141140 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139892, d141140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12318 q selected
    | true =>
      simp only [d139892, d141140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12319 q selected
  have h2 (q : Pattern) (selected : d139894 q = 1) : d139894 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d139895 q = 1) : d141141 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139895, d141141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139895, d141141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d139896 q = 1) : d141142 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139896, d141142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139896, d141142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139897 q = 1) : d141143 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139897, d141143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139897, d141143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139901 q = 1) : d141147 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139901, d141147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139901, d141147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12320 q selected
  have h8 (q : Pattern) (selected : d139902 q = 1) : d141148 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139902, d141148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d139902, d141148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d139903 q = 1) : d141149 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139903, d141149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139903, d141149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d139904 q = 1) : d141150 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139904, d141150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d139904, d141150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d139905 q = 1) : d141151 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139905, d141151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d139905, d141151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d139912 q = 1) : d141157 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139912, d141157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139912, d141157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12321 q selected
  have h13 (q : Pattern) (selected : d139913 q = 1) : d141158 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139913, d141158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d139913, d141158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d139914 q = 1) : d141159 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139914, d141159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139914, d141159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d139915 q = 1) : d141160 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139915, d141160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d139915, d141160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d139916 q = 1) : d141161 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139916, d141161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d139916, d141161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d139917 q = 1) : d141162 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d139917, d141162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d139917, d141162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro12323 (p : Pattern) (selected : d139923 p = 1) : d141168 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d139918 q = 1) : d141163 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d139918, d141163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139918, d141163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12322 q selected
  have h2 (q : Pattern) (selected : d139919 q = 1) : d141164 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d139919, d141164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139919, d141164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d139920 q = 1) : d141165 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d139920, d141165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139920, d141165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139921 q = 1) : d141166 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d139921, d141166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139921, d141166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d139922 q = 1) : d141167 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d139922, d141167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139922, d141167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139923 q = 1) : d141168 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d139923, d141168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139923, d141168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12324 (p : Pattern) (selected : d139932 p = 1) : d141176 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78480 q = 1) : d78480 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d78486 q = 1) : d78486 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d139927 q = 1) : d139927 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d78506 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4140 q selected
    | true =>
      simp only [d78506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139928 q = 1) : d141172 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139928, d141172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139928, d141172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139929 q = 1) : d141173 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139929, d141173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139929, d141173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d139930 q = 1) : d141174 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139930, d141174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d139930, d141174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d139931 q = 1) : d141175 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139931, d141175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139931, d141175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d139932 q = 1) : d141176 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139932, d141176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139932, d141176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro12325 (p : Pattern) (selected : d139938 p = 1) : d141181 p = 1 := by
  have h0 (q : Pattern) (selected : d78480 q = 1) : d78480 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78486 q = 1) : d78486 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d139927 q = 1) : d139927 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d78506 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4140 q selected
    | true =>
      simp only [d78506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d139928 q = 1) : d141172 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139928, d141172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d139928, d141172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139929 q = 1) : d141173 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139929, d141173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139929, d141173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h7 (q : Pattern) (selected : d139930 q = 1) : d141174 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139930, d141174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139930, d141174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d139931 q = 1) : d141175 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139931, d141175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139931, d141175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d78517 q = 1) : d78517 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d78521 q = 1) : d78521 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d139933 q = 1) : d139933 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d78526 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4142 q selected
    | true =>
      simp only [d78526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h13 (q : Pattern) (selected : d139934 q = 1) : d141177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139934, d141177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d139934, d141177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d139935 q = 1) : d141178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139935, d141178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139935, d141178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h15 (q : Pattern) (selected : d139936 q = 1) : d141179 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139936, d141179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139936, d141179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d139937 q = 1) : d141180 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139937, d141180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d139937, d141180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d139938 q = 1) : d141181 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139938, d141181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139938, d141181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro12326 (p : Pattern) (selected : d139947 p = 1) : d141188 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d139933 q = 1) : d139933 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d78526 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4142 q selected
    | true =>
      simp only [d78526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139934 q = 1) : d141177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139934, d141177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139934, d141177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139935 q = 1) : d141178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139935, d141178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139935, d141178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139945 q = 1) : d141186 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139945, d141186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139945, d141186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139946 q = 1) : d141187 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139946, d141187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139946, d141187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139947 q = 1) : d141188 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139947, d141188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139947, d141188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12327 (p : Pattern) (selected : d139958 p = 1) : d141198 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d139953 q = 1) : d139953 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d78571 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4146 q selected
    | true =>
      simp only [d78571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139954 q = 1) : d141194 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139954, d141194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139954, d141194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139955 q = 1) : d141195 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139955, d141195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139955, d141195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139956 q = 1) : d141196 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139956, d141196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139956, d141196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139957 q = 1) : d141197 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139957, d141197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139957, d141197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139958 q = 1) : d141198 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139958, d141198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139958, d141198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12328 (p : Pattern) (selected : d139964 p = 1) : d141204 p = 1 := by
  have h0 (q : Pattern) (selected : d78474 q = 1) : d78474 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d139939 q = 1) : d141182 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139939, d141182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12324 q selected
    | true =>
      simp only [d139939, d141182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12325 q selected
  have h2 (q : Pattern) (selected : d139941 q = 1) : d139941 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d139942 q = 1) : d141183 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139942, d141183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139942, d141183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d139943 q = 1) : d141184 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139943, d141184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139943, d141184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139944 q = 1) : d141185 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139944, d141185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139944, d141185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139948 q = 1) : d141189 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139948, d141189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139948, d141189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12326 q selected
  have h8 (q : Pattern) (selected : d139949 q = 1) : d141190 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139949, d141190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d139949, d141190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d139950 q = 1) : d141191 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139950, d141191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139950, d141191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d139951 q = 1) : d141192 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139951, d141192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d139951, d141192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d139952 q = 1) : d141193 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139952, d141193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d139952, d141193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d139959 q = 1) : d141199 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139959, d141199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139959, d141199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12327 q selected
  have h13 (q : Pattern) (selected : d139960 q = 1) : d141200 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139960, d141200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d139960, d141200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d139961 q = 1) : d141201 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139961, d141201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139961, d141201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d139962 q = 1) : d141202 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139962, d141202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d139962, d141202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d139963 q = 1) : d141203 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139963, d141203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d139963, d141203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d139964 q = 1) : d141204 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d139964, d141204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d139964, d141204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro12329 (p : Pattern) (selected : d139970 p = 1) : d141210 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d139965 q = 1) : d141205 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d139965, d141205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139965, d141205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12328 q selected
  have h2 (q : Pattern) (selected : d139966 q = 1) : d141206 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d139966, d141206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139966, d141206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d139967 q = 1) : d141207 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d139967, d141207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139967, d141207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139968 q = 1) : d141208 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d139968, d141208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139968, d141208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d139969 q = 1) : d141209 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d139969, d141209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139969, d141209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139970 q = 1) : d141210 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d139970, d141210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139970, d141210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12330 (p : Pattern) (selected : d139980 p = 1) : d141219 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78630 q = 1) : d78630 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d78636 q = 1) : d78636 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d139975 q = 1) : d139975 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d78656 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4151 q selected
    | true =>
      simp only [d78656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139976 q = 1) : d141215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139976, d141215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139976, d141215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139977 q = 1) : d141216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139977, d141216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139977, d141216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d139978 q = 1) : d141217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139978, d141217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d139978, d141217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d139979 q = 1) : d141218 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139979, d141218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139979, d141218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d139980 q = 1) : d141219 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139980, d141219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139980, d141219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro12331 (p : Pattern) (selected : d139986 p = 1) : d141224 p = 1 := by
  have h0 (q : Pattern) (selected : d78630 q = 1) : d78630 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78636 q = 1) : d78636 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d139975 q = 1) : d139975 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d78656 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4151 q selected
    | true =>
      simp only [d78656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d139976 q = 1) : d141215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139976, d141215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d139976, d141215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139977 q = 1) : d141216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139977, d141216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d139977, d141216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h7 (q : Pattern) (selected : d139978 q = 1) : d141217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139978, d141217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139978, d141217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d139979 q = 1) : d141218 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139979, d141218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139979, d141218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d78667 q = 1) : d78667 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d78671 q = 1) : d78671 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d139981 q = 1) : d139981 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d78676 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4153 q selected
    | true =>
      simp only [d78676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h13 (q : Pattern) (selected : d139982 q = 1) : d141220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139982, d141220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d139982, d141220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d139983 q = 1) : d141221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139983, d141221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d139983, d141221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h15 (q : Pattern) (selected : d139984 q = 1) : d141222 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139984, d141222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d139984, d141222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d139985 q = 1) : d141223 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139985, d141223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d139985, d141223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d139986 q = 1) : d141224 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139986, d141224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139986, d141224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro12332 (p : Pattern) (selected : d139995 p = 1) : d141231 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d139981 q = 1) : d139981 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d78676 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4153 q selected
    | true =>
      simp only [d78676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139982 q = 1) : d141220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139982, d141220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139982, d141220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139983 q = 1) : d141221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139983, d141221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139983, d141221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139993 q = 1) : d141229 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139993, d141229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139993, d141229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139994 q = 1) : d141230 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139994, d141230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139994, d141230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139995 q = 1) : d141231 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139995, d141231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139995, d141231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12333 (p : Pattern) (selected : d140006 p = 1) : d141241 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d140001 q = 1) : d140001 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d78721 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4157 q selected
    | true =>
      simp only [d78721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d140002 q = 1) : d141237 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140002, d141237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140002, d141237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d140003 q = 1) : d141238 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140003, d141238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d140003, d141238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d140004 q = 1) : d141239 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140004, d141239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d140004, d141239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d140005 q = 1) : d141240 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140005, d141240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d140005, d141240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d140006 q = 1) : d141241 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140006, d141241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d140006, d141241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12334 (p : Pattern) (selected : d140012 p = 1) : d141247 p = 1 := by
  have h0 (q : Pattern) (selected : d78624 q = 1) : d78624 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d139987 q = 1) : d141225 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139987, d141225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12330 q selected
    | true =>
      simp only [d139987, d141225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12331 q selected
  have h2 (q : Pattern) (selected : d139989 q = 1) : d139989 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d139990 q = 1) : d141226 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139990, d141226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139990, d141226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d139991 q = 1) : d141227 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139991, d141227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139991, d141227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139992 q = 1) : d141228 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139992, d141228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139992, d141228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139996 q = 1) : d141232 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139996, d141232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d139996, d141232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12332 q selected
  have h8 (q : Pattern) (selected : d139997 q = 1) : d141233 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139997, d141233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d139997, d141233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d139998 q = 1) : d141234 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139998, d141234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d139998, d141234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d139999 q = 1) : d141235 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139999, d141235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d139999, d141235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d140000 q = 1) : d141236 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d140000, d141236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d140000, d141236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d140007 q = 1) : d141242 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140007, d141242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d140007, d141242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12333 q selected
  have h13 (q : Pattern) (selected : d140008 q = 1) : d141243 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d140008, d141243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d140008, d141243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d140009 q = 1) : d141244 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d140009, d141244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d140009, d141244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d140010 q = 1) : d141245 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d140010, d141245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d140010, d141245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d140011 q = 1) : d141246 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d140011, d141246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d140011, d141246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d140012 q = 1) : d141247 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d140012, d141247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d140012, d141247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro12335 (p : Pattern) (selected : d140018 p = 1) : d141253 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d140013 q = 1) : d141248 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d140013, d141248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d140013, d141248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12334 q selected
  have h2 (q : Pattern) (selected : d140014 q = 1) : d141249 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d140014, d141249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d140014, d141249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d140015 q = 1) : d141250 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d140015, d141250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d140015, d141250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d140016 q = 1) : d141251 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d140016, d141251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d140016, d141251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d140017 q = 1) : d141252 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d140017, d141252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d140017, d141252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d140018 q = 1) : d141253 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d140018, d141253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d140018, d141253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12336 (p : Pattern) (selected : d140024 p = 1) : d141259 p = 1 := by
  have h0 (q : Pattern) (selected : d139833 q = 1) : d141088 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d139833, d141088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12305 q selected
    | true =>
      simp only [d139833, d141088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12311 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d139878 q = 1) : d141128 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d139878, d141128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139878, d141128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12317 q selected
  have h3 (q : Pattern) (selected : d139879 q = 1) : d141129 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d139879, d141129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d139879, d141129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d139924 q = 1) : d141169 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d139924, d141169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139924, d141169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12323 q selected
  have h5 (q : Pattern) (selected : d139925 q = 1) : d141170 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d139925, d141170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139925, d141170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d139926 q = 1) : d141171 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d139926, d141171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d139926, d141171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d139971 q = 1) : d141211 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d139971, d141211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139971, d141211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12329 q selected
  have h8 (q : Pattern) (selected : d139972 q = 1) : d141212 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d139972, d141212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139972, d141212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d139973 q = 1) : d141213 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d139973, d141213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d139973, d141213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d139974 q = 1) : d141214 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d139974, d141214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d139974, d141214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d140019 q = 1) : d141254 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d140019, d141254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140019, d141254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12335 q selected
  have h12 (q : Pattern) (selected : d140020 q = 1) : d141255 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d140020, d141255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140020, d141255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d140021 q = 1) : d141256 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d140021, d141256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140021, d141256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d140022 q = 1) : d141257 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d140022, d141257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140022, d141257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d140023 q = 1) : d141258 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d140023, d141258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d140023, d141258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d140024 q = 1) : d141259 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d140024, d141259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d140024, d141259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro12337 (p : Pattern) (selected : d140030 p = 1) : d141265 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d140025 q = 1) : d141260 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d140025, d141260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12336 q selected
    | true =>
      simp only [d140025, d141260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d140026 q = 1) : d141261 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d140026, d141261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140026, d141261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d140027 q = 1) : d141262 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d140027, d141262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d140027, d141262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d140028 q = 1) : d141263 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d140028, d141263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d140028, d141263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d140029 q = 1) : d141264 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d140029, d141264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d140029, d141264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d140030 q = 1) : d141265 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d140030, d141265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d140030, d141265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12338 (p : Pattern) (selected : d140036 p = 1) : d141271 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d140031 q = 1) : d141266 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d140031, d141266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12337 q selected
    | true =>
      simp only [d140031, d141266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d140032 q = 1) : d141267 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d140032, d141267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140032, d141267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d140033 q = 1) : d141268 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d140033, d141268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d140033, d141268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d140034 q = 1) : d141269 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d140034, d141269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d140034, d141269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d140035 q = 1) : d141270 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d140035, d141270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d140035, d141270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d140036 q = 1) : d141271 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d140036, d141271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d140036, d141271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12339 (p : Pattern) (selected : d140042 p = 1) : d141277 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d140037 q = 1) : d141272 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d140037, d141272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12338 q selected
    | true =>
      simp only [d140037, d141272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d140038 q = 1) : d141273 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d140038, d141273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140038, d141273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d140039 q = 1) : d141274 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d140039, d141274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d140039, d141274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d140040 q = 1) : d141275 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d140040, d141275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d140040, d141275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d140041 q = 1) : d141276 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d140041, d141276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d140041, d141276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d140042 q = 1) : d141277 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d140042, d141277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d140042, d141277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12340 (p : Pattern) (selected : d140048 p = 1) : d141283 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d140043 q = 1) : d141278 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d140043, d141278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12339 q selected
    | true =>
      simp only [d140043, d141278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d140044 q = 1) : d141279 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d140044, d141279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140044, d141279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d140045 q = 1) : d141280 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d140045, d141280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d140045, d141280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d140046 q = 1) : d141281 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d140046, d141281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d140046, d141281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d140047 q = 1) : d141282 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d140047, d141282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d140047, d141282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d140048 q = 1) : d141283 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d140048, d141283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d140048, d141283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12341 (p : Pattern) (selected : d140054 p = 1) : d141289 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d140049 q = 1) : d141284 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d140049, d141284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12340 q selected
    | true =>
      simp only [d140049, d141284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d140050 q = 1) : d141285 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d140050, d141285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140050, d141285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d140051 q = 1) : d141286 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d140051, d141286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d140051, d141286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d140052 q = 1) : d141287 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d140052, d141287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d140052, d141287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d140053 q = 1) : d141288 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d140053, d141288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d140053, d141288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d140054 q = 1) : d141289 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d140054, d141289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d140054, d141289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12342 (p : Pattern) (selected : d140060 p = 1) : d141295 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d140055 q = 1) : d141290 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d140055, d141290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12341 q selected
    | true =>
      simp only [d140055, d141290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d140056 q = 1) : d141291 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d140056, d141291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140056, d141291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d140057 q = 1) : d141292 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d140057, d141292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d140057, d141292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d140058 q = 1) : d141293 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d140058, d141293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d140058, d141293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d140059 q = 1) : d141294 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d140059, d141294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d140059, d141294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d140060 q = 1) : d141295 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d140060, d141295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d140060, d141295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12343 (p : Pattern) (selected : d140066 p = 1) : d141301 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d140061 q = 1) : d141296 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d140061, d141296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12342 q selected
    | true =>
      simp only [d140061, d141296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d140062 q = 1) : d141297 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d140062, d141297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140062, d141297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d140063 q = 1) : d141298 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d140063, d141298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d140063, d141298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d140064 q = 1) : d141299 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d140064, d141299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d140064, d141299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d140065 q = 1) : d141300 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d140065, d141300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d140065, d141300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d140066 q = 1) : d141301 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d140066, d141301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d140066, d141301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12344 (p : Pattern) (selected : d28 p = 0) : d51880 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d27 q = 0) : d51879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d28 q = 0) : d51880 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12345 (p : Pattern) (selected : d142672 p = 0) : d144109 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142667 q = 0) : d144104 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142667, d144104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12344 q selected
    | true =>
      simp only [d142667, d144104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142668 q = 0) : d144105 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142668, d144105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142668, d144105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142669 q = 0) : d144106 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142669, d144106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142669, d144106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142670 q = 0) : d144107 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142670, d144107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142670, d144107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142671 q = 0) : d144108 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d142671, d144108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142671, d144108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142672 q = 0) : d144109 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d142672, d144109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142672, d144109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12346 (p : Pattern) (selected : d142678 p = 0) : d144115 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142673 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12345 q selected
    | true =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142674 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142675 q = 0) : d144112 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142675, d144112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142675, d144112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142676 q = 0) : d144113 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142676, d144113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142676, d144113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142677 q = 0) : d144114 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142677, d144114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142677, d144114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142678 q = 0) : d144115 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142678, d144115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142678, d144115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12347 (p : Pattern) (selected : d142684 p = 0) : d144121 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142679 q = 0) : d144116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
    | true =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142680 q = 0) : d144117 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142680, d144117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142680, d144117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d142681 q = 0) : d144118 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142681, d144118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142681, d144118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142682 q = 0) : d144119 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142682, d144119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142682, d144119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142683 q = 0) : d144120 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142683, d144120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142683, d144120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142684 q = 0) : d144121 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142684, d144121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142684, d144121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12348 (p : Pattern) (selected : d142685 p = 0) : d144122 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142673 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12345 q selected
    | true =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142674 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142675 q = 0) : d144112 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142675, d144112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142675, d144112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142676 q = 0) : d144113 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142676, d144113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142676, d144113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142677 q = 0) : d144114 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142677, d144114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142677, d144114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142685 q = 0) : d144122 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142685, d144122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142685, d144122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12349 (p : Pattern) (selected : d142691 p = 0) : d144128 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142679 q = 0) : d144116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
    | true =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142680 q = 0) : d144117 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142680, d144117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142680, d144117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d142681 q = 0) : d144118 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142681, d144118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142681, d144118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142682 q = 0) : d144119 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142682, d144119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142682, d144119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142683 q = 0) : d144120 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142683, d144120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142683, d144120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142686 q = 0) : d144123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142686, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12348 q selected
    | true =>
      simp only [d142686, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d142687 q = 0) : d144124 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142687, d144124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142687, d144124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142688 q = 0) : d144125 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142688, d144125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142688, d144125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d142689 q = 0) : d144126 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142689, d144126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142689, d144126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142690 q = 0) : d144127 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142690, d144127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142690, d144127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d142691 q = 0) : d144128 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142691, d144128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142691, d144128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro12350 (p : Pattern) (selected : d142696 p = 0) : d144133 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142686 q = 0) : d144123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142686, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12348 q selected
    | true =>
      simp only [d142686, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142687 q = 0) : d144124 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142687, d144124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142687, d144124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d142688 q = 0) : d144125 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142688, d144125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142688, d144125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142689 q = 0) : d144126 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142689, d144126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142689, d144126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142690 q = 0) : d144127 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142690, d144127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142690, d144127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142696 q = 0) : d144133 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142696, d144133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142696, d144133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12351 (p : Pattern) (selected : d69 p = 0) : d51921 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66 q = 0) : d51918 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
  have h2 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d67 q = 0) : d51919 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d68 q = 0) : d51920 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d69 q = 0) : d51921 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12352 (p : Pattern) (selected : d142707 p = 0) : d144144 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142702 q = 0) : d144139 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142702, d144139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12351 q selected
    | true =>
      simp only [d142702, d144139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142703 q = 0) : d144140 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142703, d144140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142703, d144140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142704 q = 0) : d144141 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142704, d144141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142704, d144141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142705 q = 0) : d144142 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142705, d144142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142705, d144142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142706 q = 0) : d144143 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d142706, d144143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142706, d144143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142707 q = 0) : d144144 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d142707, d144144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142707, d144144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12353 (p : Pattern) (selected : d142713 p = 0) : d144150 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142708 q = 0) : d144145 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142708, d144145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12352 q selected
    | true =>
      simp only [d142708, d144145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142709 q = 0) : d144146 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142709, d144146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142709, d144146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142710 q = 0) : d144147 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142710, d144147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142710, d144147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142711 q = 0) : d144148 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142711, d144148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142711, d144148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142712 q = 0) : d144149 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142712, d144149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142712, d144149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142713 q = 0) : d144150 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142713, d144150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142713, d144150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12354 (p : Pattern) (selected : d142719 p = 0) : d144156 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142714 q = 0) : d144151 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142714, d144151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12353 q selected
    | true =>
      simp only [d142714, d144151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142715 q = 0) : d144152 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142715, d144152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142715, d144152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d142716 q = 0) : d144153 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142716, d144153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142716, d144153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142717 q = 0) : d144154 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142717, d144154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142717, d144154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142718 q = 0) : d144155 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142718, d144155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142718, d144155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142719 q = 0) : d144156 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142719, d144156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142719, d144156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12355 (p : Pattern) (selected : d142725 p = 0) : d144162 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142692 q = 0) : d144129 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142692, d144129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12347 q selected
    | true =>
      simp only [d142692, d144129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12349 q selected
  have h2 (q : Pattern) (selected : d142693 q = 0) : d144130 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d142693, d144130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142693, d144130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d142694 q = 0) : d144131 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d142694, d144131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142694, d144131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142695 q = 0) : d144132 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d142695, d144132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142695, d144132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142697 q = 0) : d144134 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142697, d144134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142697, d144134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12350 q selected
  have h6 (q : Pattern) (selected : d142698 q = 0) : d144135 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d142698, d144135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142698, d144135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d142699 q = 0) : d144136 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d142699, d144136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142699, d144136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142700 q = 0) : d144137 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d142700, d144137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142700, d144137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d142701 q = 0) : d144138 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d142701, d144138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142701, d144138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142720 q = 0) : d144157 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142720, d144157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142720, d144157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12354 q selected
  have h11 (q : Pattern) (selected : d142721 q = 0) : d144158 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d142721, d144158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d142721, d144158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d142722 q = 0) : d144159 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d142722, d144159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d142722, d144159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d142723 q = 0) : d144160 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d142723, d144160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d142723, d144160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d142724 q = 0) : d144161 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d142724, d144161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d142724, d144161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d142725 q = 0) : d144162 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d142725, d144162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d142725, d144162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro12356 (p : Pattern) (selected : d142735 p = 0) : d144172 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142679 q = 0) : d144116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
    | true =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142731 q = 0) : d144168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142731, d144168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142731, d144168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142732 q = 0) : d144169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142732, d144169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142732, d144169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142733 q = 0) : d144170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142733, d144170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142733, d144170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142734 q = 0) : d144171 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142734, d144171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142734, d144171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142735 q = 0) : d144172 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142735, d144172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142735, d144172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12357 (p : Pattern) (selected : d142742 p = 0) : d144179 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142679 q = 0) : d144116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
    | true =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142731 q = 0) : d144168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142731, d144168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142731, d144168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142732 q = 0) : d144169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142732, d144169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142732, d144169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142733 q = 0) : d144170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142733, d144170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142733, d144170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142734 q = 0) : d144171 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142734, d144171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142734, d144171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142686 q = 0) : d144123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142686, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12348 q selected
    | true =>
      simp only [d142686, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d142738 q = 0) : d144175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142738, d144175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142738, d144175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142739 q = 0) : d144176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142739, d144176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142739, d144176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d142740 q = 0) : d144177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142740, d144177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142740, d144177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142741 q = 0) : d144178 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142741, d144178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142741, d144178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d142742 q = 0) : d144179 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142742, d144179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142742, d144179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro12358 (p : Pattern) (selected : d142747 p = 0) : d144184 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142673 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12345 q selected
    | true =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142674 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142675 q = 0) : d144112 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142675, d144112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142675, d144112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142676 q = 0) : d144113 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142676, d144113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142676, d144113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142746 q = 0) : d144183 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142746, d144183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142746, d144183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142747 q = 0) : d144184 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142747, d144184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142747, d144184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12359 (p : Pattern) (selected : d142754 p = 0) : d144191 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142673 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12345 q selected
    | true =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142674 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142675 q = 0) : d144112 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142675, d144112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142675, d144112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142752 q = 0) : d144189 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142752, d144189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142752, d144189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142753 q = 0) : d144190 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142753, d144190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142753, d144190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142754 q = 0) : d144191 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142754, d144191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142754, d144191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12360 (p : Pattern) (selected : d142 p = 0) : d51993 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d139 q = 0) : d51990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro205 q selected
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d140 q = 0) : d51991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d141 q = 0) : d51992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142 q = 0) : d51993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12361 (p : Pattern) (selected : d142763 p = 0) : d144200 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142758 q = 0) : d144195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142758, d144195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12360 q selected
    | true =>
      simp only [d142758, d144195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12344 q selected
  have h2 (q : Pattern) (selected : d142759 q = 0) : d144196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142759, d144196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142759, d144196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142760 q = 0) : d144197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142760, d144197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142760, d144197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142667 q = 0) : d144104 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142667, d144104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12344 q selected
    | true =>
      simp only [d142667, d144104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142668 q = 0) : d144105 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142668, d144105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142668, d144105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142669 q = 0) : d144106 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142669, d144106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142669, d144106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142761 q = 0) : d144198 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142761, d144198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142761, d144198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142670 q = 0) : d144107 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142670, d144107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142670, d144107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d142762 q = 0) : d144199 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d142762, d144199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142762, d144199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142763 q = 0) : d144200 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d142763, d144200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d142763, d144200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12362 (p : Pattern) (selected : d142769 p = 0) : d144206 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142764 q = 0) : d144201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12361 q selected
    | true =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142765 q = 0) : d144202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142673 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12345 q selected
    | true =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142674 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142766 q = 0) : d144203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142766, d144203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142766, d144203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142767 q = 0) : d144204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142767, d144204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142767, d144204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d142768 q = 0) : d144205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142768, d144205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142768, d144205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142769 q = 0) : d144206 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142769, d144206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142769, d144206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12363 (p : Pattern) (selected : d173 p = 0) : d51880 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d170 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d171 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172 q = 0) : d51879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173 q = 0) : d51880 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12364 (p : Pattern) (selected : d142776 p = 0) : d144109 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142771 q = 0) : d144104 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142771, d144104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12363 q selected
    | true =>
      simp only [d142771, d144104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142772 q = 0) : d144105 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142772, d144105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142772, d144105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142773 q = 0) : d144106 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142773, d144106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142773, d144106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142774 q = 0) : d144107 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142774, d144107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142774, d144107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142775 q = 0) : d144108 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d142775, d144108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142775, d144108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142776 q = 0) : d144109 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d142776, d144109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142776, d144109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12365 (p : Pattern) (selected : d142782 p = 0) : d144115 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142777 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142777, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12364 q selected
    | true =>
      simp only [d142777, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142778 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142778, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142778, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142779 q = 0) : d144112 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142779, d144112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142779, d144112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142780 q = 0) : d144113 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142780, d144113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142780, d144113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142781 q = 0) : d144114 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142781, d144114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142781, d144114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142782 q = 0) : d144115 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142782, d144115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142782, d144115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12366 (p : Pattern) (selected : d142788 p = 0) : d144212 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142748 q = 0) : d144185 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142748, d144185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12358 q selected
    | true =>
      simp only [d142748, d144185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142749 q = 0) : d144186 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142749, d144186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142749, d144186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142750 q = 0) : d144187 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142750, d144187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142750, d144187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142751 q = 0) : d144188 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142751, d144188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142751, d144188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142755 q = 0) : d144192 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142755, d144192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12359 q selected
    | true =>
      simp only [d142755, d144192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142756 q = 0) : d144193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142756, d144193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142756, d144193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142757 q = 0) : d144194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142757, d144194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142757, d144194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142770 q = 0) : d144207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142770, d144207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12362 q selected
    | true =>
      simp only [d142770, d144207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
  have h9 (q : Pattern) (selected : d142783 q = 0) : d144116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142783, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12365 q selected
    | true =>
      simp only [d142783, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d142784 q = 0) : d144208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142784, d144208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d142784, d144208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d142679 q = 0) : d144116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
    | true =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d142680 q = 0) : d144117 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142680, d144117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d142680, d144117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d142785 q = 0) : d144209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142785, d144209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d142785, d144209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d142786 q = 0) : d144210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142786, d144210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142786, d144210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d142787 q = 0) : d144211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142787, d144211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142787, d144211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d142788 q = 0) : d144212 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142788, d144212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142788, d144212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro12367 (p : Pattern) (selected : d142789 p = 0) : d144213 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142673 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12345 q selected
    | true =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142674 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142675 q = 0) : d144112 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142675, d144112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142675, d144112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142676 q = 0) : d144113 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142676, d144113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142676, d144113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142746 q = 0) : d144183 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142746, d144183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142746, d144183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142789 q = 0) : d144213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142789, d144213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142789, d144213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12368 (p : Pattern) (selected : d142794 p = 0) : d144218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142673 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12345 q selected
    | true =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142674 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142675 q = 0) : d144112 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142675, d144112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142675, d144112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142752 q = 0) : d144189 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142752, d144189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142752, d144189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142753 q = 0) : d144190 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142753, d144190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142753, d144190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142794 q = 0) : d144218 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142794, d144218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142794, d144218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12369 (p : Pattern) (selected : d142798 p = 0) : d144222 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142764 q = 0) : d144201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12361 q selected
    | true =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142765 q = 0) : d144202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142673 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12345 q selected
    | true =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142674 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142766 q = 0) : d144203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142766, d144203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142766, d144203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142767 q = 0) : d144204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142767, d144204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142767, d144204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d142768 q = 0) : d144205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142768, d144205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142768, d144205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142798 q = 0) : d144222 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142798, d144222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142798, d144222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12370 (p : Pattern) (selected : d142800 p = 0) : d144122 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142777 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142777, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12364 q selected
    | true =>
      simp only [d142777, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142778 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142778, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142778, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142779 q = 0) : d144112 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142779, d144112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142779, d144112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142780 q = 0) : d144113 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142780, d144113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142780, d144113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142781 q = 0) : d144114 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142781, d144114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142781, d144114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142800 q = 0) : d144122 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142800, d144122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142800, d144122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12371 (p : Pattern) (selected : d142806 p = 0) : d144228 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142748 q = 0) : d144185 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142748, d144185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12358 q selected
    | true =>
      simp only [d142748, d144185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142749 q = 0) : d144186 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142749, d144186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142749, d144186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142750 q = 0) : d144187 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142750, d144187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142750, d144187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142751 q = 0) : d144188 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142751, d144188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142751, d144188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142755 q = 0) : d144192 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142755, d144192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12359 q selected
    | true =>
      simp only [d142755, d144192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142756 q = 0) : d144193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142756, d144193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142756, d144193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142757 q = 0) : d144194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142757, d144194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142757, d144194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142770 q = 0) : d144207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142770, d144207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12362 q selected
    | true =>
      simp only [d142770, d144207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
  have h9 (q : Pattern) (selected : d142783 q = 0) : d144116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142783, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12365 q selected
    | true =>
      simp only [d142783, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d142784 q = 0) : d144208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142784, d144208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d142784, d144208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d142679 q = 0) : d144116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
    | true =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d142680 q = 0) : d144117 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142680, d144117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d142680, d144117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d142785 q = 0) : d144209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142785, d144209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d142785, d144209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d142786 q = 0) : d144210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142786, d144210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142786, d144210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d142787 q = 0) : d144211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142787, d144211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142787, d144211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d142790 q = 0) : d144214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142790, d144214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12367 q selected
    | true =>
      simp only [d142790, d144214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d142791 q = 0) : d144215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142791, d144215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142791, d144215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d142792 q = 0) : d144216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142792, d144216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d142792, d144216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d142793 q = 0) : d144217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142793, d144217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142793, d144217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d142795 q = 0) : d144219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142795, d144219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12368 q selected
    | true =>
      simp only [d142795, d144219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d142796 q = 0) : d144220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142796, d144220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142796, d144220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d142797 q = 0) : d144221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142797, d144221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d142797, d144221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d142799 q = 0) : d144223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142799, d144223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12369 q selected
    | true =>
      simp only [d142799, d144223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12348 q selected
  have h24 (q : Pattern) (selected : d142801 q = 0) : d144123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142801, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12370 q selected
    | true =>
      simp only [d142801, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d142802 q = 0) : d144224 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142802, d144224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d142802, d144224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d142686 q = 0) : d144123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142686, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12348 q selected
    | true =>
      simp only [d142686, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d142687 q = 0) : d144124 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142687, d144124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d142687, d144124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d142803 q = 0) : d144225 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142803, d144225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d142803, d144225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d142804 q = 0) : d144226 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142804, d144226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d142804, d144226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d142805 q = 0) : d144227 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142805, d144227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d142805, d144227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d142806 q = 0) : d144228 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142806, d144228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d142806, d144228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro12372 (p : Pattern) (selected : d142808 p = 0) : d144230 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142679 q = 0) : d144116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
    | true =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142731 q = 0) : d144168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142731, d144168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142731, d144168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142732 q = 0) : d144169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142732, d144169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142732, d144169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142733 q = 0) : d144170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142733, d144170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142733, d144170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142734 q = 0) : d144171 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142734, d144171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142734, d144171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142808 q = 0) : d144230 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142808, d144230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142808, d144230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12373 (p : Pattern) (selected : d142815 p = 0) : d144237 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142799 q = 0) : d144223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142799, d144223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12369 q selected
    | true =>
      simp only [d142799, d144223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12348 q selected
  have h2 (q : Pattern) (selected : d142801 q = 0) : d144123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142801, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12370 q selected
    | true =>
      simp only [d142801, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d142802 q = 0) : d144224 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142802, d144224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142802, d144224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142686 q = 0) : d144123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142686, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12348 q selected
    | true =>
      simp only [d142686, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142687 q = 0) : d144124 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142687, d144124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142687, d144124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142803 q = 0) : d144225 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142803, d144225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142803, d144225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142813 q = 0) : d144235 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142813, d144235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142813, d144235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142814 q = 0) : d144236 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142814, d144236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142814, d144236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d142815 q = 0) : d144237 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142815, d144237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142815, d144237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro12374 (p : Pattern) (selected : d229 p = 0) : d52047 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226 q = 0) : d52044 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro205 q selected
  have h2 (q : Pattern) (selected : d139 q = 0) : d51990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro205 q selected
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227 q = 0) : d52045 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d140 q = 0) : d51991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228 q = 0) : d52046 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229 q = 0) : d52047 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12375 (p : Pattern) (selected : d142826 p = 0) : d144248 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142821 q = 0) : d144243 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142821, d144243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12374 q selected
    | true =>
      simp only [d142821, d144243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12351 q selected
  have h2 (q : Pattern) (selected : d142822 q = 0) : d144244 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142822, d144244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142822, d144244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142823 q = 0) : d144245 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142823, d144245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142823, d144245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142702 q = 0) : d144139 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142702, d144139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12351 q selected
    | true =>
      simp only [d142702, d144139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142703 q = 0) : d144140 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142703, d144140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142703, d144140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142704 q = 0) : d144141 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142704, d144141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142704, d144141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142824 q = 0) : d144246 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142824, d144246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142824, d144246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142705 q = 0) : d144142 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142705, d144142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142705, d144142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d142825 q = 0) : d144247 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d142825, d144247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142825, d144247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142826 q = 0) : d144248 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d142826, d144248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d142826, d144248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12376 (p : Pattern) (selected : d142832 p = 0) : d144254 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142827 q = 0) : d144249 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142827, d144249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12375 q selected
    | true =>
      simp only [d142827, d144249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142828 q = 0) : d144250 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142828, d144250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142828, d144250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142708 q = 0) : d144145 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142708, d144145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12352 q selected
    | true =>
      simp only [d142708, d144145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142709 q = 0) : d144146 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142709, d144146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142709, d144146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142829 q = 0) : d144251 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142829, d144251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142829, d144251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142830 q = 0) : d144252 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142830, d144252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142830, d144252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d142831 q = 0) : d144253 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142831, d144253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142831, d144253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142832 q = 0) : d144254 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142832, d144254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142832, d144254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12377 (p : Pattern) (selected : d248 p = 0) : d51921 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d245 q = 0) : d51918 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
  have h2 (q : Pattern) (selected : d170 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246 q = 0) : d51919 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d171 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247 q = 0) : d51920 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d248 q = 0) : d51921 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248, d51921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d248, d51921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12378 (p : Pattern) (selected : d142839 p = 0) : d144144 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142834 q = 0) : d144139 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142834, d144139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12377 q selected
    | true =>
      simp only [d142834, d144139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142835 q = 0) : d144140 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142835, d144140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142835, d144140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142836 q = 0) : d144141 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142836, d144141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142836, d144141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142837 q = 0) : d144142 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142837, d144142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142837, d144142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142838 q = 0) : d144143 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d142838, d144143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142838, d144143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142839 q = 0) : d144144 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d142839, d144144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142839, d144144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12379 (p : Pattern) (selected : d142845 p = 0) : d144150 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142840 q = 0) : d144145 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142840, d144145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12378 q selected
    | true =>
      simp only [d142840, d144145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142841 q = 0) : d144146 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142841, d144146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142841, d144146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142842 q = 0) : d144147 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142842, d144147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142842, d144147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142843 q = 0) : d144148 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142843, d144148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142843, d144148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142844 q = 0) : d144149 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142844, d144149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142844, d144149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142845 q = 0) : d144150 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142845, d144150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142845, d144150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12380 (p : Pattern) (selected : d142851 p = 0) : d144260 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142833 q = 0) : d144255 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142833, d144255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12376 q selected
    | true =>
      simp only [d142833, d144255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12353 q selected
  have h2 (q : Pattern) (selected : d142846 q = 0) : d144151 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142846, d144151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12379 q selected
    | true =>
      simp only [d142846, d144151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d142847 q = 0) : d144256 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142847, d144256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142847, d144256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142714 q = 0) : d144151 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142714, d144151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12353 q selected
    | true =>
      simp only [d142714, d144151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142715 q = 0) : d144152 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142715, d144152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142715, d144152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142848 q = 0) : d144257 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142848, d144257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142848, d144257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142849 q = 0) : d144258 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142849, d144258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142849, d144258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142850 q = 0) : d144259 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142850, d144259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142850, d144259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d142851 q = 0) : d144260 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142851, d144260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142851, d144260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro12381 (p : Pattern) (selected : d142857 p = 0) : d144266 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142736 q = 0) : d144173 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142736, d144173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142736, d144173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12356 q selected
  have h2 (q : Pattern) (selected : d142737 q = 0) : d144174 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d142737, d144174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142737, d144174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d142743 q = 0) : d144180 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142743, d144180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12356 q selected
    | true =>
      simp only [d142743, d144180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12357 q selected
  have h4 (q : Pattern) (selected : d142744 q = 0) : d144181 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d142744, d144181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142744, d144181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142745 q = 0) : d144182 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d142745, d144182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142745, d144182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142807 q = 0) : d144229 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142807, d144229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12366 q selected
    | true =>
      simp only [d142807, d144229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12371 q selected
  have h7 (q : Pattern) (selected : d142809 q = 0) : d144231 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142809, d144231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12372 q selected
    | true =>
      simp only [d142809, d144231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142810 q = 0) : d144232 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d142810, d144232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142810, d144232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d142811 q = 0) : d144233 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d142811, d144233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d142811, d144233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d142812 q = 0) : d144234 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d142812, d144234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142812, d144234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d142816 q = 0) : d144238 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142816, d144238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142816, d144238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12373 q selected
  have h12 (q : Pattern) (selected : d142817 q = 0) : d144239 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d142817, d144239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d142817, d144239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d142818 q = 0) : d144240 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d142818, d144240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d142818, d144240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d142819 q = 0) : d144241 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d142819, d144241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d142819, d144241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d142820 q = 0) : d144242 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d142820, d144242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d142820, d144242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d142852 q = 0) : d144261 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142852, d144261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142852, d144261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12380 q selected
  have h17 (q : Pattern) (selected : d142853 q = 0) : d144262 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d142853, d144262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d142853, d144262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d142854 q = 0) : d144263 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d142854, d144263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d142854, d144263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d142855 q = 0) : d144264 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d142855, d144264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d142855, d144264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d142856 q = 0) : d144265 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d142856, d144265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d142856, d144265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d142857 q = 0) : d144266 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d142857, d144266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d142857, d144266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro12382 (p : Pattern) (selected : d142863 p = 0) : d144272 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142726 q = 0) : d144163 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d142726, d144163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142726, d144163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12355 q selected
  have h2 (q : Pattern) (selected : d142727 q = 0) : d144164 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d142727, d144164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142727, d144164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142728 q = 0) : d144165 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d142728, d144165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142728, d144165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142729 q = 0) : d144166 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d142729, d144166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142729, d144166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142730 q = 0) : d144167 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d142730, d144167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142730, d144167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142858 q = 0) : d144267 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d142858, d144267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142858, d144267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12381 q selected
  have h7 (q : Pattern) (selected : d142859 q = 0) : d144268 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d142859, d144268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142859, d144268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142860 q = 0) : d144269 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d142860, d144269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142860, d144269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d142861 q = 0) : d144270 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d142861, d144270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142861, d144270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142862 q = 0) : d144271 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d142862, d144271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142862, d144271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d142863 q = 0) : d144272 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d142863, d144272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142863, d144272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro12383 (p : Pattern) (selected : d142868 p = 0) : d144277 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142770 q = 0) : d144207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142770, d144207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12362 q selected
    | true =>
      simp only [d142770, d144207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
  have h2 (q : Pattern) (selected : d142864 q = 0) : d144273 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142864, d144273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142864, d144273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142865 q = 0) : d144274 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142865, d144274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142865, d144274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142866 q = 0) : d144275 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142866, d144275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142866, d144275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142867 q = 0) : d144276 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142867, d144276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142867, d144276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142868 q = 0) : d144277 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142868, d144277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142868, d144277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12384 (p : Pattern) (selected : d142875 p = 0) : d144284 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142770 q = 0) : d144207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142770, d144207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12362 q selected
    | true =>
      simp only [d142770, d144207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
  have h2 (q : Pattern) (selected : d142864 q = 0) : d144273 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142864, d144273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142864, d144273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142865 q = 0) : d144274 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142865, d144274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142865, d144274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142866 q = 0) : d144275 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142866, d144275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142866, d144275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142867 q = 0) : d144276 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142867, d144276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142867, d144276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142799 q = 0) : d144223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142799, d144223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12369 q selected
    | true =>
      simp only [d142799, d144223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12348 q selected
  have h7 (q : Pattern) (selected : d142871 q = 0) : d144280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142871, d144280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142871, d144280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142872 q = 0) : d144281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142872, d144281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142872, d144281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d142873 q = 0) : d144282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142873, d144282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142873, d144282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142874 q = 0) : d144283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142874, d144283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142874, d144283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d142875 q = 0) : d144284 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142875, d144284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142875, d144284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro12385 (p : Pattern) (selected : d142880 p = 0) : d144289 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142764 q = 0) : d144201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12361 q selected
    | true =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142765 q = 0) : d144202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142673 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12345 q selected
    | true =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142674 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142766 q = 0) : d144203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142766, d144203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142766, d144203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142767 q = 0) : d144204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142767, d144204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142767, d144204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d142879 q = 0) : d144288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142879, d144288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142879, d144288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142880 q = 0) : d144289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142880, d144289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142880, d144289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12386 (p : Pattern) (selected : d142887 p = 0) : d144296 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142764 q = 0) : d144201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12361 q selected
    | true =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142765 q = 0) : d144202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142673 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12345 q selected
    | true =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142674 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142766 q = 0) : d144203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142766, d144203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142766, d144203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142885 q = 0) : d144294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142885, d144294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142885, d144294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142886 q = 0) : d144295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142886, d144295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142886, d144295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142887 q = 0) : d144296 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142887, d144296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142887, d144296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12387 (p : Pattern) (selected : d322 p = 0) : d52121 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d319 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d320 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d321 q = 0) : d52120 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d322 q = 0) : d52121 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12388 (p : Pattern) (selected : d142896 p = 0) : d144305 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142891 q = 0) : d144300 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142891, d144300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12387 q selected
    | true =>
      simp only [d142891, d144300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12360 q selected
  have h2 (q : Pattern) (selected : d142892 q = 0) : d144301 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142892, d144301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142892, d144301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142893 q = 0) : d144302 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142893, d144302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142893, d144302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142758 q = 0) : d144195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142758, d144195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12360 q selected
    | true =>
      simp only [d142758, d144195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12344 q selected
  have h5 (q : Pattern) (selected : d142759 q = 0) : d144196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142759, d144196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142759, d144196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142760 q = 0) : d144197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142760, d144197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142760, d144197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142894 q = 0) : d144303 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142894, d144303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142894, d144303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142667 q = 0) : d144104 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142667, d144104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12344 q selected
    | true =>
      simp only [d142667, d144104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d142668 q = 0) : d144105 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142668, d144105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142668, d144105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142669 q = 0) : d144106 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142669, d144106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142669, d144106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d142761 q = 0) : d144198 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142761, d144198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142761, d144198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d142895 q = 0) : d144304 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d142895, d144304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142895, d144304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d142896 q = 0) : d144305 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d142896, d144305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d142896, d144305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro12389 (p : Pattern) (selected : d142902 p = 0) : d144311 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142897 q = 0) : d144306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142897, d144306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12388 q selected
    | true =>
      simp only [d142897, d144306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142898 q = 0) : d144307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142898, d144307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142898, d144307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142764 q = 0) : d144201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12361 q selected
    | true =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142765 q = 0) : d144202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142899 q = 0) : d144308 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142899, d144308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142899, d144308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142900 q = 0) : d144309 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142900, d144309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142900, d144309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d142901 q = 0) : d144310 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142901, d144310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142901, d144310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142902 q = 0) : d144311 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142902, d144311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142902, d144311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12390 (p : Pattern) (selected : d353 p = 0) : d51993 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d350 q = 0) : d51990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro240 q selected
    | true =>
      simp only [d350, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351 q = 0) : d51991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d351, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352 q = 0) : d51992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352, d51992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352, d51992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d353 q = 0) : d51993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d353, d51993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d353, d51993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12391 (p : Pattern) (selected : d142909 p = 0) : d144200 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142904 q = 0) : d144195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142904, d144195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12390 q selected
    | true =>
      simp only [d142904, d144195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12363 q selected
  have h2 (q : Pattern) (selected : d142905 q = 0) : d144196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142905, d144196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142905, d144196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142906 q = 0) : d144197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142906, d144197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142906, d144197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142771 q = 0) : d144104 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142771, d144104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12363 q selected
    | true =>
      simp only [d142771, d144104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142772 q = 0) : d144105 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142772, d144105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142772, d144105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142773 q = 0) : d144106 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142773, d144106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142773, d144106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142907 q = 0) : d144198 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142907, d144198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142907, d144198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142774 q = 0) : d144107 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142774, d144107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142774, d144107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d142908 q = 0) : d144199 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d142908, d144199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142908, d144199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142909 q = 0) : d144200 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d142909, d144200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d142909, d144200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12392 (p : Pattern) (selected : d142915 p = 0) : d144206 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142910 q = 0) : d144201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142910, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12391 q selected
    | true =>
      simp only [d142910, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142911 q = 0) : d144202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142911, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142911, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142777 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142777, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12364 q selected
    | true =>
      simp only [d142777, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142778 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142778, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142778, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142912 q = 0) : d144203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142912, d144203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142912, d144203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142913 q = 0) : d144204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142913, d144204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142913, d144204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d142914 q = 0) : d144205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142914, d144205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142914, d144205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142915 q = 0) : d144206 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142915, d144206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142915, d144206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12393 (p : Pattern) (selected : d142921 p = 0) : d144317 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142764 q = 0) : d144201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12361 q selected
    | true =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142765 q = 0) : d144202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142918 q = 0) : d144314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142918, d144314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142918, d144314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142919 q = 0) : d144315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142919, d144315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142919, d144315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142920 q = 0) : d144316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142920, d144316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142920, d144316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142921 q = 0) : d144317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142921, d144317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142921, d144317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12394 (p : Pattern) (selected : d142927 p = 0) : d144323 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142881 q = 0) : d144290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142881, d144290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12385 q selected
    | true =>
      simp only [d142881, d144290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12358 q selected
  have h2 (q : Pattern) (selected : d142882 q = 0) : d144291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142882, d144291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142882, d144291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142883 q = 0) : d144292 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142883, d144292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142883, d144292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142884 q = 0) : d144293 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142884, d144293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142884, d144293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142888 q = 0) : d144297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142888, d144297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12386 q selected
    | true =>
      simp only [d142888, d144297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12359 q selected
  have h6 (q : Pattern) (selected : d142889 q = 0) : d144298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142889, d144298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142889, d144298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142890 q = 0) : d144299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142890, d144299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142890, d144299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142903 q = 0) : d144312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142903, d144312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12389 q selected
    | true =>
      simp only [d142903, d144312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12362 q selected
  have h9 (q : Pattern) (selected : d142916 q = 0) : d144207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142916, d144207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12392 q selected
    | true =>
      simp only [d142916, d144207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12365 q selected
  have h10 (q : Pattern) (selected : d142917 q = 0) : d144313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142917, d144313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d142917, d144313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d142922 q = 0) : d144318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142922, d144318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12393 q selected
    | true =>
      simp only [d142922, d144318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d142923 q = 0) : d144319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142923, d144319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d142923, d144319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d142924 q = 0) : d144320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142924, d144320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d142924, d144320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d142925 q = 0) : d144321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142925, d144321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142925, d144321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d142926 q = 0) : d144322 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142926, d144322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142926, d144322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d142927 q = 0) : d144323 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142927, d144323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142927, d144323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro12395 (p : Pattern) (selected : d142928 p = 0) : d144324 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142764 q = 0) : d144201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12361 q selected
    | true =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142765 q = 0) : d144202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142673 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12345 q selected
    | true =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142674 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142766 q = 0) : d144203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142766, d144203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142766, d144203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142767 q = 0) : d144204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142767, d144204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142767, d144204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d142879 q = 0) : d144288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142879, d144288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142879, d144288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142928 q = 0) : d144324 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142928, d144324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142928, d144324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12396 (p : Pattern) (selected : d142933 p = 0) : d144329 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142764 q = 0) : d144201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12361 q selected
    | true =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142765 q = 0) : d144202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142673 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12345 q selected
    | true =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142674 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142766 q = 0) : d144203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142766, d144203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142766, d144203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142885 q = 0) : d144294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142885, d144294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142885, d144294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142886 q = 0) : d144295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142886, d144295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142886, d144295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142933 q = 0) : d144329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142933, d144329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142933, d144329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12397 (p : Pattern) (selected : d142937 p = 0) : d144333 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142897 q = 0) : d144306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142897, d144306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12388 q selected
    | true =>
      simp only [d142897, d144306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142898 q = 0) : d144307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142898, d144307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142898, d144307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142764 q = 0) : d144201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12361 q selected
    | true =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142765 q = 0) : d144202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142899 q = 0) : d144308 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142899, d144308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142899, d144308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142900 q = 0) : d144309 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142900, d144309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142900, d144309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d142901 q = 0) : d144310 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142901, d144310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142901, d144310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142937 q = 0) : d144333 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142937, d144333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142937, d144333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12398 (p : Pattern) (selected : d142939 p = 0) : d144222 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142910 q = 0) : d144201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142910, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12391 q selected
    | true =>
      simp only [d142910, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142911 q = 0) : d144202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142911, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142911, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142777 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142777, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12364 q selected
    | true =>
      simp only [d142777, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142778 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142778, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142778, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142912 q = 0) : d144203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142912, d144203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142912, d144203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142913 q = 0) : d144204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142913, d144204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142913, d144204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d142914 q = 0) : d144205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142914, d144205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142914, d144205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142939 q = 0) : d144222 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142939, d144222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142939, d144222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12399 (p : Pattern) (selected : d142942 p = 0) : d144336 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142764 q = 0) : d144201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12361 q selected
    | true =>
      simp only [d142764, d144201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142765 q = 0) : d144202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142765, d144202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142918 q = 0) : d144314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142918, d144314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142918, d144314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142919 q = 0) : d144315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142919, d144315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142919, d144315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142920 q = 0) : d144316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142920, d144316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142920, d144316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142942 q = 0) : d144336 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142942, d144336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142942, d144336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12400 (p : Pattern) (selected : d142948 p = 0) : d144342 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142881 q = 0) : d144290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142881, d144290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12385 q selected
    | true =>
      simp only [d142881, d144290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12358 q selected
  have h2 (q : Pattern) (selected : d142882 q = 0) : d144291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142882, d144291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142882, d144291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142883 q = 0) : d144292 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142883, d144292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142883, d144292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142884 q = 0) : d144293 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142884, d144293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142884, d144293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142888 q = 0) : d144297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142888, d144297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12386 q selected
    | true =>
      simp only [d142888, d144297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12359 q selected
  have h6 (q : Pattern) (selected : d142889 q = 0) : d144298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142889, d144298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142889, d144298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142890 q = 0) : d144299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142890, d144299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142890, d144299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142903 q = 0) : d144312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142903, d144312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12389 q selected
    | true =>
      simp only [d142903, d144312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12362 q selected
  have h9 (q : Pattern) (selected : d142916 q = 0) : d144207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142916, d144207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12392 q selected
    | true =>
      simp only [d142916, d144207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12365 q selected
  have h10 (q : Pattern) (selected : d142917 q = 0) : d144313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142917, d144313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d142917, d144313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d142922 q = 0) : d144318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142922, d144318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12393 q selected
    | true =>
      simp only [d142922, d144318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d142923 q = 0) : d144319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142923, d144319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d142923, d144319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d142924 q = 0) : d144320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142924, d144320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d142924, d144320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d142925 q = 0) : d144321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142925, d144321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142925, d144321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d142926 q = 0) : d144322 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142926, d144322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142926, d144322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d142929 q = 0) : d144325 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142929, d144325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12395 q selected
    | true =>
      simp only [d142929, d144325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12367 q selected
  have h17 (q : Pattern) (selected : d142930 q = 0) : d144326 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142930, d144326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142930, d144326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d142931 q = 0) : d144327 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142931, d144327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d142931, d144327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d142932 q = 0) : d144328 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142932, d144328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142932, d144328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d142934 q = 0) : d144330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142934, d144330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12396 q selected
    | true =>
      simp only [d142934, d144330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12368 q selected
  have h21 (q : Pattern) (selected : d142935 q = 0) : d144331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142935, d144331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142935, d144331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d142936 q = 0) : d144332 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142936, d144332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d142936, d144332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d142938 q = 0) : d144334 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142938, d144334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12397 q selected
    | true =>
      simp only [d142938, d144334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12369 q selected
  have h24 (q : Pattern) (selected : d142940 q = 0) : d144223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142940, d144223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12398 q selected
    | true =>
      simp only [d142940, d144223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12370 q selected
  have h25 (q : Pattern) (selected : d142941 q = 0) : d144335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142941, d144335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d142941, d144335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d142943 q = 0) : d144337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142943, d144337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12399 q selected
    | true =>
      simp only [d142943, d144337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d142944 q = 0) : d144338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142944, d144338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d142944, d144338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d142945 q = 0) : d144339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142945, d144339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d142945, d144339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d142946 q = 0) : d144340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142946, d144340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d142946, d144340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d142947 q = 0) : d144341 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142947, d144341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d142947, d144341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d142948 q = 0) : d144342 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142948, d144342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d142948, d144342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro12401 (p : Pattern) (selected : d142950 p = 0) : d144344 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142770 q = 0) : d144207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142770, d144207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12362 q selected
    | true =>
      simp only [d142770, d144207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
  have h2 (q : Pattern) (selected : d142864 q = 0) : d144273 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142864, d144273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142864, d144273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142865 q = 0) : d144274 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142865, d144274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142865, d144274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142866 q = 0) : d144275 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142866, d144275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142866, d144275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142867 q = 0) : d144276 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142867, d144276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142867, d144276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142679 q = 0) : d144116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
    | true =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d142731 q = 0) : d144168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142731, d144168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142731, d144168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142732 q = 0) : d144169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142732, d144169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142732, d144169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d142733 q = 0) : d144170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142733, d144170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142733, d144170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142734 q = 0) : d144171 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142734, d144171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142734, d144171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d142950 q = 0) : d144344 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142950, d144344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142950, d144344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro12402 (p : Pattern) (selected : d142957 p = 0) : d144351 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142938 q = 0) : d144334 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142938, d144334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12397 q selected
    | true =>
      simp only [d142938, d144334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12369 q selected
  have h2 (q : Pattern) (selected : d142940 q = 0) : d144223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142940, d144223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12398 q selected
    | true =>
      simp only [d142940, d144223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12370 q selected
  have h3 (q : Pattern) (selected : d142941 q = 0) : d144335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142941, d144335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142941, d144335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142943 q = 0) : d144337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142943, d144337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12399 q selected
    | true =>
      simp only [d142943, d144337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142944 q = 0) : d144338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142944, d144338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142944, d144338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142945 q = 0) : d144339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142945, d144339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142945, d144339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142955 q = 0) : d144349 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142955, d144349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142955, d144349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142956 q = 0) : d144350 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142956, d144350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142956, d144350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d142957 q = 0) : d144351 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142957, d144351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142957, d144351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro12403 (p : Pattern) (selected : d142959 p = 0) : d144353 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142686 q = 0) : d144123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142686, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12348 q selected
    | true =>
      simp only [d142686, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142738 q = 0) : d144175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142738, d144175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142738, d144175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142739 q = 0) : d144176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142739, d144176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142739, d144176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142740 q = 0) : d144177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142740, d144177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142740, d144177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142741 q = 0) : d144178 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142741, d144178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142741, d144178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142959 q = 0) : d144353 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142959, d144353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142959, d144353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12404 (p : Pattern) (selected : d415 p = 0) : d52181 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d412 q = 0) : d52178 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
  have h2 (q : Pattern) (selected : d319 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d413 q = 0) : d52179 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d320 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d414 q = 0) : d52180 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d415 q = 0) : d52181 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12405 (p : Pattern) (selected : d142970 p = 0) : d144364 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142965 q = 0) : d144359 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142965, d144359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12404 q selected
    | true =>
      simp only [d142965, d144359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12374 q selected
  have h2 (q : Pattern) (selected : d142966 q = 0) : d144360 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142966, d144360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142966, d144360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142967 q = 0) : d144361 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142967, d144361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142967, d144361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142821 q = 0) : d144243 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142821, d144243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12374 q selected
    | true =>
      simp only [d142821, d144243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12351 q selected
  have h5 (q : Pattern) (selected : d142822 q = 0) : d144244 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142822, d144244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142822, d144244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142823 q = 0) : d144245 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142823, d144245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142823, d144245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142968 q = 0) : d144362 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142968, d144362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142968, d144362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142702 q = 0) : d144139 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142702, d144139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12351 q selected
    | true =>
      simp only [d142702, d144139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d142703 q = 0) : d144140 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142703, d144140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142703, d144140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142704 q = 0) : d144141 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142704, d144141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142704, d144141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d142824 q = 0) : d144246 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142824, d144246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142824, d144246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d142969 q = 0) : d144363 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d142969, d144363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142969, d144363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d142970 q = 0) : d144364 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d142970, d144364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d142970, d144364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro12406 (p : Pattern) (selected : d142976 p = 0) : d144370 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142971 q = 0) : d144365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142971, d144365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12405 q selected
    | true =>
      simp only [d142971, d144365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142972 q = 0) : d144366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142972, d144366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142972, d144366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142827 q = 0) : d144249 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142827, d144249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12375 q selected
    | true =>
      simp only [d142827, d144249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142828 q = 0) : d144250 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142828, d144250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142828, d144250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142973 q = 0) : d144367 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142973, d144367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142973, d144367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142974 q = 0) : d144368 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142974, d144368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142974, d144368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d142975 q = 0) : d144369 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142975, d144369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142975, d144369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142976 q = 0) : d144370 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142976, d144370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142976, d144370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12407 (p : Pattern) (selected : d434 p = 0) : d52047 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d431 q = 0) : d52044 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d431, d52044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d431, d52044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro240 q selected
  have h2 (q : Pattern) (selected : d350 q = 0) : d51990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro240 q selected
    | true =>
      simp only [d350, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d432 q = 0) : d52045 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d432, d52045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d432, d52045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351 q = 0) : d51991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d433 q = 0) : d52046 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d433, d52046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d433, d52046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d434 q = 0) : d52047 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d434, d52047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d434, d52047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12408 (p : Pattern) (selected : d142983 p = 0) : d144248 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142978 q = 0) : d144243 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142978, d144243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12407 q selected
    | true =>
      simp only [d142978, d144243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12377 q selected
  have h2 (q : Pattern) (selected : d142979 q = 0) : d144244 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142979, d144244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142979, d144244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142980 q = 0) : d144245 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142980, d144245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142980, d144245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142834 q = 0) : d144139 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142834, d144139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12377 q selected
    | true =>
      simp only [d142834, d144139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142835 q = 0) : d144140 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142835, d144140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142835, d144140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142836 q = 0) : d144141 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142836, d144141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142836, d144141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142981 q = 0) : d144246 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142981, d144246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142981, d144246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142837 q = 0) : d144142 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142837, d144142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142837, d144142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d142982 q = 0) : d144247 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d142982, d144247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142982, d144247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142983 q = 0) : d144248 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d142983, d144248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d142983, d144248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12409 (p : Pattern) (selected : d142989 p = 0) : d144254 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142984 q = 0) : d144249 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142984, d144249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12408 q selected
    | true =>
      simp only [d142984, d144249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142985 q = 0) : d144250 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142985, d144250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142985, d144250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142840 q = 0) : d144145 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142840, d144145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12378 q selected
    | true =>
      simp only [d142840, d144145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142841 q = 0) : d144146 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142841, d144146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142841, d144146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142986 q = 0) : d144251 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142986, d144251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142986, d144251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142987 q = 0) : d144252 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142987, d144252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142987, d144252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d142988 q = 0) : d144253 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142988, d144253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142988, d144253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142989 q = 0) : d144254 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142989, d144254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142989, d144254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12410 (p : Pattern) (selected : d142995 p = 0) : d144376 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142827 q = 0) : d144249 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142827, d144249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12375 q selected
    | true =>
      simp only [d142827, d144249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142828 q = 0) : d144250 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142828, d144250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142828, d144250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142992 q = 0) : d144373 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142992, d144373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142992, d144373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142993 q = 0) : d144374 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142993, d144374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142993, d144374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142994 q = 0) : d144375 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142994, d144375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142994, d144375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142995 q = 0) : d144376 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142995, d144376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142995, d144376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12411 (p : Pattern) (selected : d143001 p = 0) : d144382 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142977 q = 0) : d144371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142977, d144371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12406 q selected
    | true =>
      simp only [d142977, d144371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12376 q selected
  have h2 (q : Pattern) (selected : d142990 q = 0) : d144255 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142990, d144255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12409 q selected
    | true =>
      simp only [d142990, d144255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12379 q selected
  have h3 (q : Pattern) (selected : d142991 q = 0) : d144372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142991, d144372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142991, d144372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142996 q = 0) : d144377 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142996, d144377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12410 q selected
    | true =>
      simp only [d142996, d144377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142997 q = 0) : d144378 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142997, d144378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142997, d144378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142998 q = 0) : d144379 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142998, d144379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142998, d144379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142999 q = 0) : d144380 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142999, d144380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142999, d144380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143000 q = 0) : d144381 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143000, d144381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143000, d144381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d143001 q = 0) : d144382 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143001, d144382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143001, d144382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro12412 (p : Pattern) (selected : d143007 p = 0) : d144388 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142714 q = 0) : d144151 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142714, d144151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12353 q selected
    | true =>
      simp only [d142714, d144151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143003 q = 0) : d144384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143003, d144384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143003, d144384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143004 q = 0) : d144385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143004, d144385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143004, d144385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143005 q = 0) : d144386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143005, d144386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143005, d144386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143006 q = 0) : d144387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143006, d144387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143006, d144387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143007 q = 0) : d144388 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143007, d144388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143007, d144388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12413 (p : Pattern) (selected : d143013 p = 0) : d144394 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142869 q = 0) : d144278 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142869, d144278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142869, d144278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12383 q selected
  have h2 (q : Pattern) (selected : d142870 q = 0) : d144279 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d142870, d144279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142870, d144279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d142876 q = 0) : d144285 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142876, d144285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12383 q selected
    | true =>
      simp only [d142876, d144285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12384 q selected
  have h4 (q : Pattern) (selected : d142877 q = 0) : d144286 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d142877, d144286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142877, d144286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142878 q = 0) : d144287 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d142878, d144287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142878, d144287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142949 q = 0) : d144343 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142949, d144343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12394 q selected
    | true =>
      simp only [d142949, d144343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12400 q selected
  have h7 (q : Pattern) (selected : d142951 q = 0) : d144345 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142951, d144345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12401 q selected
    | true =>
      simp only [d142951, d144345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12357 q selected
  have h8 (q : Pattern) (selected : d142952 q = 0) : d144346 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d142952, d144346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142952, d144346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d142953 q = 0) : d144347 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d142953, d144347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d142953, d144347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d142954 q = 0) : d144348 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d142954, d144348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142954, d144348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d142958 q = 0) : d144352 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142958, d144352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142958, d144352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12402 q selected
  have h12 (q : Pattern) (selected : d142960 q = 0) : d144354 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142960, d144354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142960, d144354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12403 q selected
  have h13 (q : Pattern) (selected : d142961 q = 0) : d144355 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d142961, d144355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d142961, d144355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d142962 q = 0) : d144356 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d142962, d144356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d142962, d144356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d142963 q = 0) : d144357 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d142963, d144357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d142963, d144357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d142964 q = 0) : d144358 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d142964, d144358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d142964, d144358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d143002 q = 0) : d144383 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143002, d144383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143002, d144383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12411 q selected
  have h18 (q : Pattern) (selected : d143008 q = 0) : d144389 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143008, d144389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143008, d144389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12412 q selected
  have h19 (q : Pattern) (selected : d143009 q = 0) : d144390 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143009, d144390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d143009, d144390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d143010 q = 0) : d144391 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143010, d144391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d143010, d144391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d143011 q = 0) : d144392 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143011, d144392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d143011, d144392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d143012 q = 0) : d144393 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d143012, d144393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d143012, d144393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d143013 q = 0) : d144394 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d143013, d144394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d143013, d144394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro12414 (p : Pattern) (selected : d143019 p = 0) : d144400 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143014 q = 0) : d144395 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d143014, d144395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143014, d144395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12413 q selected
  have h2 (q : Pattern) (selected : d143015 q = 0) : d144396 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d143015, d144396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143015, d144396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143016 q = 0) : d144397 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d143016, d144397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143016, d144397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143017 q = 0) : d144398 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d143017, d144398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143017, d144398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143018 q = 0) : d144399 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d143018, d144399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143018, d144399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143019 q = 0) : d144400 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d143019, d144400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143019, d144400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12415 (p : Pattern) (selected : d754 p = 0) : d52431 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d753 q = 0) : d52430 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d754 q = 0) : d52431 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12416 (p : Pattern) (selected : d143030 p = 0) : d144411 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143021 q = 0) : d144402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143021, d144402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12387 q selected
    | true =>
      simp only [d143021, d144402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12415 q selected
  have h2 (q : Pattern) (selected : d143022 q = 0) : d144403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143022, d144403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143022, d144403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143023 q = 0) : d144404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143023, d144404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143023, d144404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143024 q = 0) : d144405 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143024, d144405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12415 q selected
    | true =>
      simp only [d143024, d144405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143025 q = 0) : d144406 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143025, d144406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143025, d144406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143026 q = 0) : d144407 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143026, d144407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143026, d144407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143027 q = 0) : d144408 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143027, d144408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143027, d144408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143028 q = 0) : d144409 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143028, d144409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143028, d144409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143029 q = 0) : d144410 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143029, d144410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143029, d144410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143030 q = 0) : d144411 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143030, d144411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143030, d144411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12417 (p : Pattern) (selected : d143034 p = 0) : d144415 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143024 q = 0) : d144405 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143024, d144405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12415 q selected
    | true =>
      simp only [d143024, d144405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143025 q = 0) : d144406 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143025, d144406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143025, d144406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143026 q = 0) : d144407 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143026, d144407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143026, d144407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143028 q = 0) : d144409 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143028, d144409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143028, d144409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143033 q = 0) : d144414 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143033, d144414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143033, d144414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143034 q = 0) : d144415 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143034, d144415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143034, d144415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12418 (p : Pattern) (selected : d143040 p = 0) : d144421 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143031 q = 0) : d144412 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12416 q selected
    | true =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143032 q = 0) : d144413 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143035 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12417 q selected
    | true =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143036 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143037 q = 0) : d144418 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143037, d144418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143037, d144418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143038 q = 0) : d144419 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143038, d144419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143038, d144419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143039 q = 0) : d144420 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143039, d144420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143039, d144420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143040 q = 0) : d144421 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143040, d144421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143040, d144421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12419 (p : Pattern) (selected : d143044 p = 0) : d144425 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143035 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12417 q selected
    | true =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143036 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143041 q = 0) : d144422 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143041, d144422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143041, d144422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143042 q = 0) : d144423 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143042, d144423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143042, d144423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143043 q = 0) : d144424 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143043, d144424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143043, d144424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143044 q = 0) : d144425 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143044, d144425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143044, d144425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12420 (p : Pattern) (selected : d143050 p = 0) : d144431 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143045 q = 0) : d144426 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143045, d144426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12418 q selected
    | true =>
      simp only [d143045, d144426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12419 q selected
  have h2 (q : Pattern) (selected : d143046 q = 0) : d144427 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143046, d144427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143046, d144427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143047 q = 0) : d144428 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143047, d144428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143047, d144428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143048 q = 0) : d144429 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143048, d144429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143048, d144429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143049 q = 0) : d144430 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143049, d144430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143049, d144430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143050 q = 0) : d144431 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143050, d144431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143050, d144431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12421 (p : Pattern) (selected : d143053 p = 0) : d144434 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143031 q = 0) : d144412 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12416 q selected
    | true =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143032 q = 0) : d144413 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143035 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12417 q selected
    | true =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143036 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143037 q = 0) : d144418 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143037, d144418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143037, d144418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143038 q = 0) : d144419 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143038, d144419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143038, d144419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143039 q = 0) : d144420 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143039, d144420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143039, d144420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143053 q = 0) : d144434 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143053, d144434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143053, d144434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12422 (p : Pattern) (selected : d143054 p = 0) : d144435 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143035 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12417 q selected
    | true =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143036 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143041 q = 0) : d144422 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143041, d144422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143041, d144422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143042 q = 0) : d144423 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143042, d144423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143042, d144423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143043 q = 0) : d144424 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143043, d144424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143043, d144424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143054 q = 0) : d144435 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143054, d144435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143054, d144435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12423 (p : Pattern) (selected : d143060 p = 0) : d144441 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143045 q = 0) : d144426 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143045, d144426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12418 q selected
    | true =>
      simp only [d143045, d144426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12419 q selected
  have h2 (q : Pattern) (selected : d143046 q = 0) : d144427 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143046, d144427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143046, d144427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143047 q = 0) : d144428 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143047, d144428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143047, d144428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143048 q = 0) : d144429 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143048, d144429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143048, d144429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143049 q = 0) : d144430 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143049, d144430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143049, d144430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143055 q = 0) : d144436 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143055, d144436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12421 q selected
    | true =>
      simp only [d143055, d144436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12422 q selected
  have h7 (q : Pattern) (selected : d143056 q = 0) : d144437 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143056, d144437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143056, d144437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143057 q = 0) : d144438 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143057, d144438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143057, d144438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143058 q = 0) : d144439 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143058, d144439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143058, d144439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143059 q = 0) : d144440 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143059, d144440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143059, d144440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143060 q = 0) : d144441 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143060, d144441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143060, d144441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro12424 (p : Pattern) (selected : d143065 p = 0) : d144446 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143031 q = 0) : d144412 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12416 q selected
    | true =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143032 q = 0) : d144413 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143035 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12417 q selected
    | true =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143036 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143037 q = 0) : d144418 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143037, d144418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143037, d144418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143038 q = 0) : d144419 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143038, d144419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143038, d144419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143064 q = 0) : d144445 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143064, d144445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143064, d144445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143065 q = 0) : d144446 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143065, d144446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143065, d144446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12425 (p : Pattern) (selected : d143067 p = 0) : d144448 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143035 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12417 q selected
    | true =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143036 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143041 q = 0) : d144422 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143041, d144422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143041, d144422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143042 q = 0) : d144423 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143042, d144423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143042, d144423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143066 q = 0) : d144447 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143066, d144447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143066, d144447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143067 q = 0) : d144448 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143067, d144448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143067, d144448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12426 (p : Pattern) (selected : d143074 p = 0) : d144455 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143031 q = 0) : d144412 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12416 q selected
    | true =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143032 q = 0) : d144413 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143035 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12417 q selected
    | true =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143036 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143037 q = 0) : d144418 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143037, d144418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143037, d144418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143072 q = 0) : d144453 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143072, d144453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143072, d144453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143073 q = 0) : d144454 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143073, d144454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143073, d144454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143074 q = 0) : d144455 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143074, d144455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143074, d144455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12427 (p : Pattern) (selected : d143077 p = 0) : d144458 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143035 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12417 q selected
    | true =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143036 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143041 q = 0) : d144422 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143041, d144422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143041, d144422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143075 q = 0) : d144456 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143075, d144456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143075, d144456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143076 q = 0) : d144457 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143076, d144457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143076, d144457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143077 q = 0) : d144458 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143077, d144458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143077, d144458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12428 (p : Pattern) (selected : d546 p = 0) : d52293 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d543 q = 0) : d52290 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro277 q selected
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d544 q = 0) : d52291 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d545 q = 0) : d52292 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d546 q = 0) : d52293 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12429 (p : Pattern) (selected : d143086 p = 0) : d144467 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143081 q = 0) : d144462 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143081, d144462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12428 q selected
    | true =>
      simp only [d143081, d144462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12387 q selected
  have h2 (q : Pattern) (selected : d143082 q = 0) : d144463 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143082, d144463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143082, d144463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143083 q = 0) : d144464 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143083, d144464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143083, d144464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143021 q = 0) : d144402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143021, d144402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12387 q selected
    | true =>
      simp only [d143021, d144402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12415 q selected
  have h5 (q : Pattern) (selected : d143022 q = 0) : d144403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143022, d144403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143022, d144403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143023 q = 0) : d144404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143023, d144404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143023, d144404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143084 q = 0) : d144465 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143084, d144465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143084, d144465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143024 q = 0) : d144405 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143024, d144405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12415 q selected
    | true =>
      simp only [d143024, d144405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143025 q = 0) : d144406 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143025, d144406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143025, d144406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143026 q = 0) : d144407 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143026, d144407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143026, d144407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143027 q = 0) : d144408 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143027, d144408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143027, d144408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d143085 q = 0) : d144466 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143085, d144466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143085, d144466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d143086 q = 0) : d144467 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143086, d144467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d143086, d144467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro12430 (p : Pattern) (selected : d143092 p = 0) : d144473 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143087 q = 0) : d144468 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143087, d144468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12429 q selected
    | true =>
      simp only [d143087, d144468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143088 q = 0) : d144469 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143088, d144469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143088, d144469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143031 q = 0) : d144412 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12416 q selected
    | true =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143032 q = 0) : d144413 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143089 q = 0) : d144470 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143089, d144470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143089, d144470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143090 q = 0) : d144471 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143090, d144471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143090, d144471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143091 q = 0) : d144472 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143091, d144472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143091, d144472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143092 q = 0) : d144473 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143092, d144473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143092, d144473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12431 (p : Pattern) (selected : d577 p = 0) : d52121 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d574 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
    | true =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d575 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d576 q = 0) : d52120 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d576, d52120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d576, d52120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d577 q = 0) : d52121 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d577, d52121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d577, d52121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12432 (p : Pattern) (selected : d877 p = 0) : d52431 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d874 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d875 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d876 q = 0) : d52430 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d876, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d876, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d877 q = 0) : d52431 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d877, d52431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d877, d52431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12433 (p : Pattern) (selected : d143103 p = 0) : d144411 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143094 q = 0) : d144402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143094, d144402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12431 q selected
    | true =>
      simp only [d143094, d144402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12432 q selected
  have h2 (q : Pattern) (selected : d143095 q = 0) : d144403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143095, d144403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143095, d144403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143096 q = 0) : d144404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143096, d144404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143096, d144404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143097 q = 0) : d144405 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143097, d144405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12432 q selected
    | true =>
      simp only [d143097, d144405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143098 q = 0) : d144406 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143098, d144406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143098, d144406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143099 q = 0) : d144407 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143099, d144407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143099, d144407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143100 q = 0) : d144408 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143100, d144408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143100, d144408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143101 q = 0) : d144409 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143101, d144409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143101, d144409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143102 q = 0) : d144410 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143102, d144410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143102, d144410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143103 q = 0) : d144411 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143103, d144411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143103, d144411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12434 (p : Pattern) (selected : d143107 p = 0) : d144415 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143097 q = 0) : d144405 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143097, d144405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12432 q selected
    | true =>
      simp only [d143097, d144405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143098 q = 0) : d144406 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143098, d144406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143098, d144406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143099 q = 0) : d144407 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143099, d144407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143099, d144407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143101 q = 0) : d144409 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143101, d144409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143101, d144409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143106 q = 0) : d144414 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143106, d144414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143106, d144414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143107 q = 0) : d144415 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143107, d144415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143107, d144415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12435 (p : Pattern) (selected : d143113 p = 0) : d144421 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143104 q = 0) : d144412 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143104, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12433 q selected
    | true =>
      simp only [d143104, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143105 q = 0) : d144413 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143105, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143105, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143108 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143108, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12434 q selected
    | true =>
      simp only [d143108, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143109 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143109, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143109, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143110 q = 0) : d144418 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143110, d144418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143110, d144418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143111 q = 0) : d144419 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143111, d144419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143111, d144419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143112 q = 0) : d144420 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143112, d144420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143112, d144420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143113 q = 0) : d144421 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143113, d144421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143113, d144421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12436 (p : Pattern) (selected : d143117 p = 0) : d144425 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143108 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143108, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12434 q selected
    | true =>
      simp only [d143108, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143109 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143109, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143109, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143114 q = 0) : d144422 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143114, d144422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143114, d144422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143115 q = 0) : d144423 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143115, d144423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143115, d144423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143116 q = 0) : d144424 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143116, d144424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143116, d144424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143117 q = 0) : d144425 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143117, d144425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143117, d144425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12437 (p : Pattern) (selected : d143123 p = 0) : d144479 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143031 q = 0) : d144412 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12416 q selected
    | true =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143032 q = 0) : d144413 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143120 q = 0) : d144476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143120, d144476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143120, d144476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143121 q = 0) : d144477 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143121, d144477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143121, d144477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143122 q = 0) : d144478 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143122, d144478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143122, d144478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143123 q = 0) : d144479 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143123, d144479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143123, d144479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12438 (p : Pattern) (selected : d143129 p = 0) : d144485 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143068 q = 0) : d144449 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143068, d144449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12424 q selected
    | true =>
      simp only [d143068, d144449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12425 q selected
  have h2 (q : Pattern) (selected : d143069 q = 0) : d144450 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143069, d144450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143069, d144450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143070 q = 0) : d144451 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143070, d144451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143070, d144451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143071 q = 0) : d144452 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143071, d144452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143071, d144452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143078 q = 0) : d144459 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143078, d144459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12426 q selected
    | true =>
      simp only [d143078, d144459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12427 q selected
  have h6 (q : Pattern) (selected : d143079 q = 0) : d144460 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143079, d144460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143079, d144460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143080 q = 0) : d144461 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143080, d144461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143080, d144461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143093 q = 0) : d144474 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143093, d144474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12430 q selected
    | true =>
      simp only [d143093, d144474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12418 q selected
  have h9 (q : Pattern) (selected : d143118 q = 0) : d144426 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143118, d144426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12435 q selected
    | true =>
      simp only [d143118, d144426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12436 q selected
  have h10 (q : Pattern) (selected : d143119 q = 0) : d144475 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143119, d144475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d143119, d144475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143124 q = 0) : d144480 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143124, d144480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12437 q selected
    | true =>
      simp only [d143124, d144480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d143125 q = 0) : d144481 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143125, d144481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d143125, d144481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d143126 q = 0) : d144482 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143126, d144482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143126, d144482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143127 q = 0) : d144483 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143127, d144483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143127, d144483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d143128 q = 0) : d144484 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143128, d144484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143128, d144484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143129 q = 0) : d144485 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143129, d144485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143129, d144485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro12439 (p : Pattern) (selected : d143130 p = 0) : d144486 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143031 q = 0) : d144412 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12416 q selected
    | true =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143032 q = 0) : d144413 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143035 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12417 q selected
    | true =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143036 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143037 q = 0) : d144418 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143037, d144418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143037, d144418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143038 q = 0) : d144419 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143038, d144419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143038, d144419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143064 q = 0) : d144445 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143064, d144445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143064, d144445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143130 q = 0) : d144486 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143130, d144486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143130, d144486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12440 (p : Pattern) (selected : d143131 p = 0) : d144487 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143035 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12417 q selected
    | true =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143036 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143041 q = 0) : d144422 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143041, d144422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143041, d144422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143042 q = 0) : d144423 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143042, d144423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143042, d144423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143066 q = 0) : d144447 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143066, d144447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143066, d144447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143131 q = 0) : d144487 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143131, d144487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143131, d144487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12441 (p : Pattern) (selected : d143136 p = 0) : d144492 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143031 q = 0) : d144412 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12416 q selected
    | true =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143032 q = 0) : d144413 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143035 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12417 q selected
    | true =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143036 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143037 q = 0) : d144418 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143037, d144418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143037, d144418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143072 q = 0) : d144453 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143072, d144453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143072, d144453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143073 q = 0) : d144454 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143073, d144454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143073, d144454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143136 q = 0) : d144492 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143136, d144492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143136, d144492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12442 (p : Pattern) (selected : d143137 p = 0) : d144493 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143035 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12417 q selected
    | true =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143036 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143041 q = 0) : d144422 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143041, d144422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143041, d144422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143075 q = 0) : d144456 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143075, d144456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143075, d144456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143076 q = 0) : d144457 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143076, d144457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143076, d144457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143137 q = 0) : d144493 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143137, d144493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143137, d144493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12443 (p : Pattern) (selected : d143141 p = 0) : d144497 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143087 q = 0) : d144468 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143087, d144468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12429 q selected
    | true =>
      simp only [d143087, d144468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143088 q = 0) : d144469 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143088, d144469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143088, d144469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143031 q = 0) : d144412 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12416 q selected
    | true =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143032 q = 0) : d144413 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143089 q = 0) : d144470 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143089, d144470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143089, d144470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143090 q = 0) : d144471 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143090, d144471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143090, d144471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143091 q = 0) : d144472 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143091, d144472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143091, d144472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143141 q = 0) : d144497 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143141, d144497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143141, d144497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12444 (p : Pattern) (selected : d143143 p = 0) : d144434 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143104 q = 0) : d144412 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143104, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12433 q selected
    | true =>
      simp only [d143104, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143105 q = 0) : d144413 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143105, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143105, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143108 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143108, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12434 q selected
    | true =>
      simp only [d143108, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143109 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143109, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143109, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143110 q = 0) : d144418 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143110, d144418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143110, d144418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143111 q = 0) : d144419 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143111, d144419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143111, d144419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143112 q = 0) : d144420 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143112, d144420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143112, d144420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143143 q = 0) : d144434 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143143, d144434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143143, d144434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12445 (p : Pattern) (selected : d143144 p = 0) : d144435 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143108 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143108, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12434 q selected
    | true =>
      simp only [d143108, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143109 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143109, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143109, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143114 q = 0) : d144422 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143114, d144422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143114, d144422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143115 q = 0) : d144423 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143115, d144423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143115, d144423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143116 q = 0) : d144424 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143116, d144424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143116, d144424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143144 q = 0) : d144435 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143144, d144435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143144, d144435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12446 (p : Pattern) (selected : d143147 p = 0) : d144500 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143031 q = 0) : d144412 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12416 q selected
    | true =>
      simp only [d143031, d144412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143032 q = 0) : d144413 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143032, d144413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143120 q = 0) : d144476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143120, d144476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143120, d144476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143121 q = 0) : d144477 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143121, d144477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143121, d144477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143122 q = 0) : d144478 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143122, d144478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143122, d144478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143147 q = 0) : d144500 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143147, d144500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143147, d144500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12447 (p : Pattern) (selected : d143153 p = 0) : d144506 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143068 q = 0) : d144449 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143068, d144449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12424 q selected
    | true =>
      simp only [d143068, d144449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12425 q selected
  have h2 (q : Pattern) (selected : d143069 q = 0) : d144450 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143069, d144450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143069, d144450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143070 q = 0) : d144451 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143070, d144451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143070, d144451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143071 q = 0) : d144452 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143071, d144452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143071, d144452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143078 q = 0) : d144459 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143078, d144459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12426 q selected
    | true =>
      simp only [d143078, d144459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12427 q selected
  have h6 (q : Pattern) (selected : d143079 q = 0) : d144460 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143079, d144460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143079, d144460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143080 q = 0) : d144461 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143080, d144461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143080, d144461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143093 q = 0) : d144474 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143093, d144474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12430 q selected
    | true =>
      simp only [d143093, d144474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12418 q selected
  have h9 (q : Pattern) (selected : d143118 q = 0) : d144426 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143118, d144426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12435 q selected
    | true =>
      simp only [d143118, d144426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12436 q selected
  have h10 (q : Pattern) (selected : d143119 q = 0) : d144475 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143119, d144475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d143119, d144475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143124 q = 0) : d144480 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143124, d144480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12437 q selected
    | true =>
      simp only [d143124, d144480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d143125 q = 0) : d144481 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143125, d144481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d143125, d144481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d143126 q = 0) : d144482 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143126, d144482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143126, d144482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143127 q = 0) : d144483 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143127, d144483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143127, d144483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d143128 q = 0) : d144484 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143128, d144484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143128, d144484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143132 q = 0) : d144488 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143132, d144488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12439 q selected
    | true =>
      simp only [d143132, d144488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12440 q selected
  have h17 (q : Pattern) (selected : d143133 q = 0) : d144489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143133, d144489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143133, d144489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d143134 q = 0) : d144490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143134, d144490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d143134, d144490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d143135 q = 0) : d144491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143135, d144491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143135, d144491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d143138 q = 0) : d144494 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143138, d144494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12441 q selected
    | true =>
      simp only [d143138, d144494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12442 q selected
  have h21 (q : Pattern) (selected : d143139 q = 0) : d144495 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143139, d144495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143139, d144495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d143140 q = 0) : d144496 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143140, d144496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d143140, d144496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d143142 q = 0) : d144498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143142, d144498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12443 q selected
    | true =>
      simp only [d143142, d144498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12421 q selected
  have h24 (q : Pattern) (selected : d143145 q = 0) : d144436 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143145, d144436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12444 q selected
    | true =>
      simp only [d143145, d144436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12445 q selected
  have h25 (q : Pattern) (selected : d143146 q = 0) : d144499 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143146, d144499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d143146, d144499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d143148 q = 0) : d144501 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143148, d144501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12446 q selected
    | true =>
      simp only [d143148, d144501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d143149 q = 0) : d144502 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143149, d144502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d143149, d144502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d143150 q = 0) : d144503 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143150, d144503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d143150, d144503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d143151 q = 0) : d144504 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143151, d144504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d143151, d144504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d143152 q = 0) : d144505 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143152, d144505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d143152, d144505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d143153 q = 0) : d144506 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143153, d144506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d143153, d144506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro12448 (p : Pattern) (selected : d143160 p = 0) : d144513 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143045 q = 0) : d144426 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143045, d144426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12418 q selected
    | true =>
      simp only [d143045, d144426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12419 q selected
  have h2 (q : Pattern) (selected : d143046 q = 0) : d144427 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143046, d144427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143046, d144427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143047 q = 0) : d144428 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143047, d144428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143047, d144428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143048 q = 0) : d144429 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143048, d144429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143048, d144429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143049 q = 0) : d144430 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143049, d144430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143049, d144430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143155 q = 0) : d144508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143155, d144508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12419 q selected
    | true =>
      simp only [d143155, d144508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143156 q = 0) : d144509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143156, d144509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143156, d144509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143157 q = 0) : d144510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143157, d144510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143157, d144510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143158 q = 0) : d144511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143158, d144511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143158, d144511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143159 q = 0) : d144512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143159, d144512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143159, d144512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143160 q = 0) : d144513 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143160, d144513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143160, d144513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro12449 (p : Pattern) (selected : d143166 p = 0) : d144519 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143155 q = 0) : d144508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143155, d144508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12419 q selected
    | true =>
      simp only [d143155, d144508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143156 q = 0) : d144509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143156, d144509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143156, d144509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143157 q = 0) : d144510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143157, d144510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143157, d144510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143158 q = 0) : d144511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143158, d144511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143158, d144511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143159 q = 0) : d144512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143159, d144512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143159, d144512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143161 q = 0) : d144514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143161, d144514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12422 q selected
    | true =>
      simp only [d143161, d144514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143162 q = 0) : d144515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143162, d144515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143162, d144515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143163 q = 0) : d144516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143163, d144516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143163, d144516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143164 q = 0) : d144517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143164, d144517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143164, d144517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143165 q = 0) : d144518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143165, d144518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143165, d144518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143166 q = 0) : d144519 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143166, d144519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143166, d144519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro12450 (p : Pattern) (selected : d143173 p = 0) : d144526 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143142 q = 0) : d144498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143142, d144498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12443 q selected
    | true =>
      simp only [d143142, d144498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12421 q selected
  have h2 (q : Pattern) (selected : d143145 q = 0) : d144436 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143145, d144436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12444 q selected
    | true =>
      simp only [d143145, d144436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12445 q selected
  have h3 (q : Pattern) (selected : d143146 q = 0) : d144499 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143146, d144499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143146, d144499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143148 q = 0) : d144501 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143148, d144501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12446 q selected
    | true =>
      simp only [d143148, d144501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143149 q = 0) : d144502 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143149, d144502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143149, d144502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143150 q = 0) : d144503 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143150, d144503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143150, d144503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143171 q = 0) : d144524 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143171, d144524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143171, d144524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143172 q = 0) : d144525 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143172, d144525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143172, d144525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d143173 q = 0) : d144526 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143173, d144526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143173, d144526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro12451 (p : Pattern) (selected : d143175 p = 0) : d144528 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143161 q = 0) : d144514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143161, d144514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12422 q selected
    | true =>
      simp only [d143161, d144514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143162 q = 0) : d144515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143162, d144515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143162, d144515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143163 q = 0) : d144516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143163, d144516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143163, d144516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143164 q = 0) : d144517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143164, d144517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143164, d144517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143165 q = 0) : d144518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143165, d144518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143165, d144518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143175 q = 0) : d144528 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143175, d144528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143175, d144528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12452 (p : Pattern) (selected : d662 p = 0) : d52366 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d659 q = 0) : d52363 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro277 q selected
  have h2 (q : Pattern) (selected : d543 q = 0) : d52290 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro277 q selected
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d660 q = 0) : d52364 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d544 q = 0) : d52291 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d661 q = 0) : d52365 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d662 q = 0) : d52366 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12453 (p : Pattern) (selected : d974 p = 0) : d52593 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d971 q = 0) : d52590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
  have h2 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d972 q = 0) : d52591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d973 q = 0) : d52592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d974 q = 0) : d52593 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12454 (p : Pattern) (selected : d143193 p = 0) : d144546 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143181 q = 0) : d144534 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143181, d144534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12452 q selected
    | true =>
      simp only [d143181, d144534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12404 q selected
  have h2 (q : Pattern) (selected : d143182 q = 0) : d144535 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143182, d144535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143182, d144535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143183 q = 0) : d144536 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143183, d144536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143183, d144536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143184 q = 0) : d144537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143184, d144537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12404 q selected
    | true =>
      simp only [d143184, d144537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12453 q selected
  have h5 (q : Pattern) (selected : d143185 q = 0) : d144538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143185, d144538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143185, d144538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143186 q = 0) : d144539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143186, d144539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143186, d144539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143187 q = 0) : d144540 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143187, d144540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143187, d144540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143188 q = 0) : d144541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143188, d144541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12453 q selected
    | true =>
      simp only [d143188, d144541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143189 q = 0) : d144542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143189, d144542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143189, d144542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143190 q = 0) : d144543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143190, d144543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143190, d144543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143191 q = 0) : d144544 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143191, d144544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143191, d144544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d143192 q = 0) : d144545 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143192, d144545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143192, d144545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d143193 q = 0) : d144546 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143193, d144546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d143193, d144546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro12455 (p : Pattern) (selected : d143198 p = 0) : d144551 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143184 q = 0) : d144537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143184, d144537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12404 q selected
    | true =>
      simp only [d143184, d144537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12453 q selected
  have h2 (q : Pattern) (selected : d143185 q = 0) : d144538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143185, d144538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143185, d144538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143186 q = 0) : d144539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143186, d144539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143186, d144539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143188 q = 0) : d144541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143188, d144541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12453 q selected
    | true =>
      simp only [d143188, d144541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143189 q = 0) : d144542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143189, d144542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143189, d144542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143190 q = 0) : d144543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143190, d144543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143190, d144543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143191 q = 0) : d144544 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143191, d144544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143191, d144544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143196 q = 0) : d144549 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143196, d144549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143196, d144549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143197 q = 0) : d144550 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143197, d144550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143197, d144550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143198 q = 0) : d144551 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143198, d144551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143198, d144551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12456 (p : Pattern) (selected : d143204 p = 0) : d144557 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143194 q = 0) : d144547 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143194, d144547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12454 q selected
    | true =>
      simp only [d143194, d144547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143195 q = 0) : d144548 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143195, d144548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143195, d144548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143199 q = 0) : d144552 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143199, d144552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12455 q selected
    | true =>
      simp only [d143199, d144552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143200 q = 0) : d144553 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143200, d144553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143200, d144553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143201 q = 0) : d144554 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143201, d144554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143201, d144554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143202 q = 0) : d144555 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143202, d144555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143202, d144555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143203 q = 0) : d144556 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143203, d144556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143203, d144556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143204 q = 0) : d144557 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143204, d144557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143204, d144557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12457 (p : Pattern) (selected : d143206 p = 0) : d144559 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143188 q = 0) : d144541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143188, d144541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12453 q selected
    | true =>
      simp only [d143188, d144541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143189 q = 0) : d144542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143189, d144542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143189, d144542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143190 q = 0) : d144543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143190, d144543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143190, d144543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143196 q = 0) : d144549 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143196, d144549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143196, d144549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143205 q = 0) : d144558 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143205, d144558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143205, d144558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143206 q = 0) : d144559 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143206, d144559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143206, d144559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12458 (p : Pattern) (selected : d143212 p = 0) : d144565 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143199 q = 0) : d144552 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143199, d144552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12455 q selected
    | true =>
      simp only [d143199, d144552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143200 q = 0) : d144553 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143200, d144553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143200, d144553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143207 q = 0) : d144560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143207, d144560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12457 q selected
    | true =>
      simp only [d143207, d144560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143208 q = 0) : d144561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143208, d144561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143208, d144561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143209 q = 0) : d144562 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143209, d144562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143209, d144562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143210 q = 0) : d144563 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143210, d144563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143210, d144563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143211 q = 0) : d144564 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143211, d144564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143211, d144564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143212 q = 0) : d144565 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143212, d144565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143212, d144565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12459 (p : Pattern) (selected : d694 p = 0) : d52181 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d691 q = 0) : d52178 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d691, d52178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d691, d52178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
  have h2 (q : Pattern) (selected : d574 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
    | true =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d692 q = 0) : d52179 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d692, d52179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d692, d52179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d575 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d693 q = 0) : d52180 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d693, d52180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d693, d52180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d694 q = 0) : d52181 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d694, d52181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d694, d52181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12460 (p : Pattern) (selected : d1021 p = 0) : d52593 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1018 q = 0) : d52590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1018, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1018, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
  have h2 (q : Pattern) (selected : d874 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1019 q = 0) : d52591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1019, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1019, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d875 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1020 q = 0) : d52592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1020, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1020, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1021 q = 0) : d52593 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1021, d52593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1021, d52593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12461 (p : Pattern) (selected : d143223 p = 0) : d144551 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143214 q = 0) : d144537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143214, d144537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12459 q selected
    | true =>
      simp only [d143214, d144537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12460 q selected
  have h2 (q : Pattern) (selected : d143215 q = 0) : d144538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143215, d144538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143215, d144538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143216 q = 0) : d144539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143216, d144539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143216, d144539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143217 q = 0) : d144541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143217, d144541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12460 q selected
    | true =>
      simp only [d143217, d144541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143218 q = 0) : d144542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143218, d144542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143218, d144542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143219 q = 0) : d144543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143219, d144543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143219, d144543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143220 q = 0) : d144544 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143220, d144544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143220, d144544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143221 q = 0) : d144549 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143221, d144549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143221, d144549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143222 q = 0) : d144550 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143222, d144550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143222, d144550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143223 q = 0) : d144551 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143223, d144551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143223, d144551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12462 (p : Pattern) (selected : d143227 p = 0) : d144559 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143217 q = 0) : d144541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143217, d144541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12460 q selected
    | true =>
      simp only [d143217, d144541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143218 q = 0) : d144542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143218, d144542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143218, d144542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143219 q = 0) : d144543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143219, d144543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143219, d144543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143221 q = 0) : d144549 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143221, d144549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143221, d144549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143226 q = 0) : d144558 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143226, d144558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143226, d144558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143227 q = 0) : d144559 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143227, d144559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143227, d144559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12463 (p : Pattern) (selected : d143233 p = 0) : d144565 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143224 q = 0) : d144552 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143224, d144552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12461 q selected
    | true =>
      simp only [d143224, d144552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143225 q = 0) : d144553 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143225, d144553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143225, d144553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143228 q = 0) : d144560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143228, d144560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12462 q selected
    | true =>
      simp only [d143228, d144560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143229 q = 0) : d144561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143229, d144561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143229, d144561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143230 q = 0) : d144562 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143230, d144562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143230, d144562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143231 q = 0) : d144563 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143231, d144563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143231, d144563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143232 q = 0) : d144564 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143232, d144564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143232, d144564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143233 q = 0) : d144565 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143233, d144565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143233, d144565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12464 (p : Pattern) (selected : d143237 p = 0) : d144570 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143228 q = 0) : d144560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143228, d144560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12462 q selected
    | true =>
      simp only [d143228, d144560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143229 q = 0) : d144561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143229, d144561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143229, d144561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143234 q = 0) : d144567 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143234, d144567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143234, d144567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143235 q = 0) : d144568 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143235, d144568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143235, d144568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143236 q = 0) : d144569 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143236, d144569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143236, d144569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143237 q = 0) : d144570 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143237, d144570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143237, d144570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12465 (p : Pattern) (selected : d143243 p = 0) : d144576 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143199 q = 0) : d144552 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143199, d144552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12455 q selected
    | true =>
      simp only [d143199, d144552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143200 q = 0) : d144553 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143200, d144553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143200, d144553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143240 q = 0) : d144573 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143240, d144573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143240, d144573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143241 q = 0) : d144574 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143241, d144574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143241, d144574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143242 q = 0) : d144575 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143242, d144575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143242, d144575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143243 q = 0) : d144576 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143243, d144576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143243, d144576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12466 (p : Pattern) (selected : d143249 p = 0) : d144582 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143213 q = 0) : d144566 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143213, d144566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12456 q selected
    | true =>
      simp only [d143213, d144566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12458 q selected
  have h2 (q : Pattern) (selected : d143238 q = 0) : d144571 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143238, d144571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12463 q selected
    | true =>
      simp only [d143238, d144571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12464 q selected
  have h3 (q : Pattern) (selected : d143239 q = 0) : d144572 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143239, d144572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143239, d144572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143244 q = 0) : d144577 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143244, d144577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12465 q selected
    | true =>
      simp only [d143244, d144577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143245 q = 0) : d144578 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143245, d144578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143245, d144578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143246 q = 0) : d144579 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143246, d144579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143246, d144579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143247 q = 0) : d144580 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143247, d144580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143247, d144580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143248 q = 0) : d144581 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143248, d144581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143248, d144581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d143249 q = 0) : d144582 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143249, d144582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143249, d144582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro12467 (p : Pattern) (selected : d143254 p = 0) : d144570 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143207 q = 0) : d144560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143207, d144560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12457 q selected
    | true =>
      simp only [d143207, d144560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143208 q = 0) : d144561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143208, d144561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143208, d144561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143251 q = 0) : d144567 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143251, d144567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143251, d144567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143252 q = 0) : d144568 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143252, d144568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143252, d144568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143253 q = 0) : d144569 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143253, d144569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143253, d144569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143254 q = 0) : d144570 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143254, d144570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143254, d144570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12468 (p : Pattern) (selected : d143260 p = 0) : d144589 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143255 q = 0) : d144584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143255, d144584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12467 q selected
    | true =>
      simp only [d143255, d144584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143256 q = 0) : d144585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143256, d144585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143256, d144585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143257 q = 0) : d144586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143257, d144586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143257, d144586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143258 q = 0) : d144587 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143258, d144587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143258, d144587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143259 q = 0) : d144588 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143259, d144588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143259, d144588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143260 q = 0) : d144589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143260, d144589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143260, d144589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12469 (p : Pattern) (selected : d143266 p = 0) : d144595 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143051 q = 0) : d144432 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143051, d144432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143051, d144432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12420 q selected
  have h2 (q : Pattern) (selected : d143052 q = 0) : d144433 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143052, d144433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143052, d144433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d143061 q = 0) : d144442 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143061, d144442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12420 q selected
    | true =>
      simp only [d143061, d144442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12423 q selected
  have h4 (q : Pattern) (selected : d143062 q = 0) : d144443 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143062, d144443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143062, d144443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143063 q = 0) : d144444 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143063, d144444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143063, d144444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143154 q = 0) : d144507 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143154, d144507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12438 q selected
    | true =>
      simp only [d143154, d144507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12447 q selected
  have h7 (q : Pattern) (selected : d143167 q = 0) : d144520 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143167, d144520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12448 q selected
    | true =>
      simp only [d143167, d144520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12449 q selected
  have h8 (q : Pattern) (selected : d143168 q = 0) : d144521 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143168, d144521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143168, d144521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d143169 q = 0) : d144522 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143169, d144522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d143169, d144522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d143170 q = 0) : d144523 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143170, d144523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143170, d144523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143174 q = 0) : d144527 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143174, d144527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143174, d144527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12450 q selected
  have h12 (q : Pattern) (selected : d143176 q = 0) : d144529 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143176, d144529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143176, d144529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12451 q selected
  have h13 (q : Pattern) (selected : d143177 q = 0) : d144530 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143177, d144530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d143177, d144530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143178 q = 0) : d144531 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143178, d144531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d143178, d144531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d143179 q = 0) : d144532 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143179, d144532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d143179, d144532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d143180 q = 0) : d144533 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d143180, d144533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143180, d144533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d143250 q = 0) : d144583 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143250, d144583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143250, d144583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12466 q selected
  have h18 (q : Pattern) (selected : d143261 q = 0) : d144590 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143261, d144590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143261, d144590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12468 q selected
  have h19 (q : Pattern) (selected : d143262 q = 0) : d144591 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143262, d144591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d143262, d144591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d143263 q = 0) : d144592 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143263, d144592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d143263, d144592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d143264 q = 0) : d144593 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143264, d144593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d143264, d144593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d143265 q = 0) : d144594 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d143265, d144594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d143265, d144594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d143266 q = 0) : d144595 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d143266, d144595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d143266, d144595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro12470 (p : Pattern) (selected : d143272 p = 0) : d144601 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143267 q = 0) : d144596 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d143267, d144596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143267, d144596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12469 q selected
  have h2 (q : Pattern) (selected : d143268 q = 0) : d144597 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d143268, d144597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143268, d144597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143269 q = 0) : d144598 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d143269, d144598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143269, d144598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143270 q = 0) : d144599 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d143270, d144599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143270, d144599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143271 q = 0) : d144600 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d143271, d144600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143271, d144600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143272 q = 0) : d144601 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d143272, d144601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143272, d144601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12471 (p : Pattern) (selected : d1113 p = 0) : d52694 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1110 q = 0) : d52691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro387 q selected
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1111 q = 0) : d52692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1112 q = 0) : d52693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1113 q = 0) : d52694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12472 (p : Pattern) (selected : d1124 p = 0) : d52705 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1121 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1122 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1123 q = 0) : d52704 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1124 q = 0) : d52705 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12473 (p : Pattern) (selected : d143284 p = 0) : d144613 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143275 q = 0) : d144604 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143275, d144604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12471 q selected
    | true =>
      simp only [d143275, d144604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12472 q selected
  have h2 (q : Pattern) (selected : d143276 q = 0) : d144605 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143276, d144605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143276, d144605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143277 q = 0) : d144606 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143277, d144606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143277, d144606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143278 q = 0) : d144607 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143278, d144607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12472 q selected
    | true =>
      simp only [d143278, d144607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143279 q = 0) : d144608 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143279, d144608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143279, d144608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143280 q = 0) : d144609 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143280, d144609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143280, d144609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143281 q = 0) : d144610 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143281, d144610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143281, d144610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143282 q = 0) : d144611 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143282, d144611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143282, d144611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143283 q = 0) : d144612 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143283, d144612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143283, d144612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143284 q = 0) : d144613 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143284, d144613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143284, d144613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12474 (p : Pattern) (selected : d143288 p = 0) : d144617 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143278 q = 0) : d144607 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143278, d144607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12472 q selected
    | true =>
      simp only [d143278, d144607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143279 q = 0) : d144608 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143279, d144608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143279, d144608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143280 q = 0) : d144609 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143280, d144609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143280, d144609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143282 q = 0) : d144611 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143282, d144611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143282, d144611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143287 q = 0) : d144616 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143287, d144616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143287, d144616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143288 q = 0) : d144617 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143288, d144617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143288, d144617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12475 (p : Pattern) (selected : d143294 p = 0) : d144623 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143285 q = 0) : d144614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12473 q selected
    | true =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143286 q = 0) : d144615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143289 q = 0) : d144618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12474 q selected
    | true =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143290 q = 0) : d144619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143291 q = 0) : d144620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143291, d144620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143291, d144620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143292 q = 0) : d144621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143292, d144621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143292, d144621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143293 q = 0) : d144622 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143293, d144622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143293, d144622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143294 q = 0) : d144623 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143294, d144623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143294, d144623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12476 (p : Pattern) (selected : d143298 p = 0) : d144627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143289 q = 0) : d144618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12474 q selected
    | true =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143290 q = 0) : d144619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143295 q = 0) : d144624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143295, d144624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143295, d144624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143296 q = 0) : d144625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143296, d144625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143296, d144625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143297 q = 0) : d144626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143297, d144626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143297, d144626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143298 q = 0) : d144627 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143298, d144627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143298, d144627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12477 (p : Pattern) (selected : d143304 p = 0) : d144633 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143299 q = 0) : d144628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143299, d144628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12475 q selected
    | true =>
      simp only [d143299, d144628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12476 q selected
  have h2 (q : Pattern) (selected : d143300 q = 0) : d144629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143300, d144629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143300, d144629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143301 q = 0) : d144630 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143301, d144630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143301, d144630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143302 q = 0) : d144631 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143302, d144631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143302, d144631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143303 q = 0) : d144632 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143303, d144632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143303, d144632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143304 q = 0) : d144633 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143304, d144633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143304, d144633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12478 (p : Pattern) (selected : d143307 p = 0) : d144636 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143285 q = 0) : d144614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12473 q selected
    | true =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143286 q = 0) : d144615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143289 q = 0) : d144618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12474 q selected
    | true =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143290 q = 0) : d144619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143291 q = 0) : d144620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143291, d144620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143291, d144620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143292 q = 0) : d144621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143292, d144621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143292, d144621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143293 q = 0) : d144622 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143293, d144622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143293, d144622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143307 q = 0) : d144636 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143307, d144636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143307, d144636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12479 (p : Pattern) (selected : d143308 p = 0) : d144637 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143289 q = 0) : d144618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12474 q selected
    | true =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143290 q = 0) : d144619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143295 q = 0) : d144624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143295, d144624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143295, d144624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143296 q = 0) : d144625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143296, d144625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143296, d144625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143297 q = 0) : d144626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143297, d144626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143297, d144626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143308 q = 0) : d144637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143308, d144637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143308, d144637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12480 (p : Pattern) (selected : d143314 p = 0) : d144643 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143299 q = 0) : d144628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143299, d144628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12475 q selected
    | true =>
      simp only [d143299, d144628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12476 q selected
  have h2 (q : Pattern) (selected : d143300 q = 0) : d144629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143300, d144629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143300, d144629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143301 q = 0) : d144630 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143301, d144630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143301, d144630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143302 q = 0) : d144631 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143302, d144631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143302, d144631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143303 q = 0) : d144632 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143303, d144632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143303, d144632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143309 q = 0) : d144638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143309, d144638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12478 q selected
    | true =>
      simp only [d143309, d144638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12479 q selected
  have h7 (q : Pattern) (selected : d143310 q = 0) : d144639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143310, d144639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143310, d144639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143311 q = 0) : d144640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143311, d144640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143311, d144640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143312 q = 0) : d144641 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143312, d144641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143312, d144641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143313 q = 0) : d144642 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143313, d144642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143313, d144642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143314 q = 0) : d144643 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143314, d144643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143314, d144643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro12481 (p : Pattern) (selected : d143319 p = 0) : d144648 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143285 q = 0) : d144614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12473 q selected
    | true =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143286 q = 0) : d144615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143289 q = 0) : d144618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12474 q selected
    | true =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143290 q = 0) : d144619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143291 q = 0) : d144620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143291, d144620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143291, d144620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143292 q = 0) : d144621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143292, d144621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143292, d144621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143318 q = 0) : d144647 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143318, d144647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143318, d144647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143319 q = 0) : d144648 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143319, d144648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143319, d144648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12482 (p : Pattern) (selected : d143321 p = 0) : d144650 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143289 q = 0) : d144618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12474 q selected
    | true =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143290 q = 0) : d144619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143295 q = 0) : d144624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143295, d144624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143295, d144624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143296 q = 0) : d144625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143296, d144625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143296, d144625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143320 q = 0) : d144649 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143320, d144649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143320, d144649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143321 q = 0) : d144650 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143321, d144650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143321, d144650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12483 (p : Pattern) (selected : d143328 p = 0) : d144657 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143285 q = 0) : d144614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12473 q selected
    | true =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143286 q = 0) : d144615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143289 q = 0) : d144618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12474 q selected
    | true =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143290 q = 0) : d144619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143291 q = 0) : d144620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143291, d144620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143291, d144620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143326 q = 0) : d144655 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143326, d144655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143326, d144655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143327 q = 0) : d144656 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143327, d144656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143327, d144656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143328 q = 0) : d144657 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143328, d144657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143328, d144657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12484 (p : Pattern) (selected : d143331 p = 0) : d144660 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143289 q = 0) : d144618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12474 q selected
    | true =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143290 q = 0) : d144619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143295 q = 0) : d144624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143295, d144624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143295, d144624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143329 q = 0) : d144658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143329, d144658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143329, d144658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143330 q = 0) : d144659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143330, d144659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143330, d144659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143331 q = 0) : d144660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143331, d144660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143331, d144660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12485 (p : Pattern) (selected : d1103 p = 0) : d52684 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1100 q = 0) : d52681 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro386 q selected
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1101 q = 0) : d52682 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1102 q = 0) : d52683 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1103 q = 0) : d52684 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d52684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1103, d52684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12486 (p : Pattern) (selected : d13028 p = 0) : d113358 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13025 q = 0) : d113355 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8289 q selected
    | true =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13026 q = 0) : d113356 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13027 q = 0) : d113357 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13027, d113357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13027, d113357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13028 q = 0) : d113358 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13028, d113358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13028, d113358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12487 (p : Pattern) (selected : d143343 p = 0) : d144672 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143335 q = 0) : d144664 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143335, d144664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12485 q selected
    | true =>
      simp only [d143335, d144664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12471 q selected
  have h2 (q : Pattern) (selected : d143336 q = 0) : d144665 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143336, d144665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143336, d144665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143337 q = 0) : d144666 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143337, d144666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143337, d144666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143338 q = 0) : d144667 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143338, d144667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12471 q selected
    | true =>
      simp only [d143338, d144667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12486 q selected
  have h5 (q : Pattern) (selected : d143339 q = 0) : d144668 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143339, d144668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143339, d144668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143340 q = 0) : d144669 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143340, d144669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143340, d144669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143341 q = 0) : d144670 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143341, d144670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143341, d144670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143275 q = 0) : d144604 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143275, d144604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12471 q selected
    | true =>
      simp only [d143275, d144604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12472 q selected
  have h9 (q : Pattern) (selected : d143276 q = 0) : d144605 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143276, d144605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143276, d144605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143277 q = 0) : d144606 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143277, d144606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143277, d144606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143278 q = 0) : d144607 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143278, d144607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12472 q selected
    | true =>
      simp only [d143278, d144607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d143279 q = 0) : d144608 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143279, d144608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143279, d144608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d143280 q = 0) : d144609 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143280, d144609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143280, d144609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143281 q = 0) : d144610 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143281, d144610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143281, d144610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d143342 q = 0) : d144671 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143342, d144671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143342, d144671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143343 q = 0) : d144672 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143343, d144672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d143343, d144672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro12488 (p : Pattern) (selected : d143349 p = 0) : d144678 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143344 q = 0) : d144673 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143344, d144673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12487 q selected
    | true =>
      simp only [d143344, d144673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143345 q = 0) : d144674 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143345, d144674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143345, d144674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143285 q = 0) : d144614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12473 q selected
    | true =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143286 q = 0) : d144615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143346 q = 0) : d144675 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143346, d144675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143346, d144675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143347 q = 0) : d144676 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143347, d144676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143347, d144676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143348 q = 0) : d144677 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143348, d144677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143348, d144677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143349 q = 0) : d144678 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143349, d144678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143349, d144678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12489 (p : Pattern) (selected : d1268 p = 0) : d52694 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1265 q = 0) : d52691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1265, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro416 q selected
    | true =>
      simp only [d1265, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1266 q = 0) : d52692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1266, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1266, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1267 q = 0) : d52693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1267, d52693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1267, d52693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1268 q = 0) : d52694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1268, d52694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1268, d52694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12490 (p : Pattern) (selected : d1279 p = 0) : d52705 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1276 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
    | true =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1277 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1278 q = 0) : d52704 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1278, d52704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1278, d52704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1279 q = 0) : d52705 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1279, d52705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1279, d52705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12491 (p : Pattern) (selected : d143360 p = 0) : d144613 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143351 q = 0) : d144604 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143351, d144604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12489 q selected
    | true =>
      simp only [d143351, d144604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12490 q selected
  have h2 (q : Pattern) (selected : d143352 q = 0) : d144605 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143352, d144605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143352, d144605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143353 q = 0) : d144606 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143353, d144606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143353, d144606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143354 q = 0) : d144607 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143354, d144607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12490 q selected
    | true =>
      simp only [d143354, d144607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143355 q = 0) : d144608 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143355, d144608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143355, d144608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143356 q = 0) : d144609 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143356, d144609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143356, d144609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143357 q = 0) : d144610 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143357, d144610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143357, d144610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143358 q = 0) : d144611 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143358, d144611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143358, d144611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143359 q = 0) : d144612 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143359, d144612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143359, d144612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143360 q = 0) : d144613 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143360, d144613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143360, d144613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12492 (p : Pattern) (selected : d143364 p = 0) : d144617 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143354 q = 0) : d144607 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143354, d144607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12490 q selected
    | true =>
      simp only [d143354, d144607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143355 q = 0) : d144608 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143355, d144608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143355, d144608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143356 q = 0) : d144609 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143356, d144609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143356, d144609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143358 q = 0) : d144611 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143358, d144611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143358, d144611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143363 q = 0) : d144616 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143363, d144616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143363, d144616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143364 q = 0) : d144617 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143364, d144617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143364, d144617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12493 (p : Pattern) (selected : d143370 p = 0) : d144623 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143361 q = 0) : d144614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143361, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12491 q selected
    | true =>
      simp only [d143361, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143362 q = 0) : d144615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143362, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143362, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143365 q = 0) : d144618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143365, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12492 q selected
    | true =>
      simp only [d143365, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143366 q = 0) : d144619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143366, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143366, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143367 q = 0) : d144620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143367, d144620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143367, d144620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143368 q = 0) : d144621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143368, d144621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143368, d144621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143369 q = 0) : d144622 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143369, d144622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143369, d144622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143370 q = 0) : d144623 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143370, d144623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143370, d144623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12494 (p : Pattern) (selected : d143374 p = 0) : d144627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143365 q = 0) : d144618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143365, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12492 q selected
    | true =>
      simp only [d143365, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143366 q = 0) : d144619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143366, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143366, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143371 q = 0) : d144624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143371, d144624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143371, d144624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143372 q = 0) : d144625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143372, d144625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143372, d144625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143373 q = 0) : d144626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143373, d144626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143373, d144626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143374 q = 0) : d144627 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143374, d144627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143374, d144627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12495 (p : Pattern) (selected : d143380 p = 0) : d144684 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143285 q = 0) : d144614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12473 q selected
    | true =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143286 q = 0) : d144615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143377 q = 0) : d144681 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143377, d144681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143377, d144681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143378 q = 0) : d144682 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143378, d144682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143378, d144682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143379 q = 0) : d144683 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143379, d144683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143379, d144683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143380 q = 0) : d144684 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143380, d144684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143380, d144684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12496 (p : Pattern) (selected : d143386 p = 0) : d144690 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143322 q = 0) : d144651 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143322, d144651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12481 q selected
    | true =>
      simp only [d143322, d144651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12482 q selected
  have h2 (q : Pattern) (selected : d143323 q = 0) : d144652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143323, d144652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143323, d144652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143324 q = 0) : d144653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143324, d144653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143324, d144653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143325 q = 0) : d144654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143325, d144654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143325, d144654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143332 q = 0) : d144661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143332, d144661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12483 q selected
    | true =>
      simp only [d143332, d144661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12484 q selected
  have h6 (q : Pattern) (selected : d143333 q = 0) : d144662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143333, d144662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143333, d144662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143334 q = 0) : d144663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143334, d144663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143334, d144663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143350 q = 0) : d144679 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143350, d144679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12488 q selected
    | true =>
      simp only [d143350, d144679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12475 q selected
  have h9 (q : Pattern) (selected : d143375 q = 0) : d144628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143375, d144628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12493 q selected
    | true =>
      simp only [d143375, d144628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12494 q selected
  have h10 (q : Pattern) (selected : d143376 q = 0) : d144680 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143376, d144680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d143376, d144680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143381 q = 0) : d144685 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143381, d144685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12495 q selected
    | true =>
      simp only [d143381, d144685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d143382 q = 0) : d144686 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143382, d144686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d143382, d144686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d143383 q = 0) : d144687 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143383, d144687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143383, d144687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143384 q = 0) : d144688 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143384, d144688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143384, d144688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d143385 q = 0) : d144689 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143385, d144689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143385, d144689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143386 q = 0) : d144690 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143386, d144690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143386, d144690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro12497 (p : Pattern) (selected : d143387 p = 0) : d144691 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143285 q = 0) : d144614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12473 q selected
    | true =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143286 q = 0) : d144615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143289 q = 0) : d144618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12474 q selected
    | true =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143290 q = 0) : d144619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143291 q = 0) : d144620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143291, d144620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143291, d144620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143292 q = 0) : d144621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143292, d144621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143292, d144621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143318 q = 0) : d144647 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143318, d144647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143318, d144647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143387 q = 0) : d144691 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143387, d144691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143387, d144691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12498 (p : Pattern) (selected : d143388 p = 0) : d144692 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143289 q = 0) : d144618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12474 q selected
    | true =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143290 q = 0) : d144619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143295 q = 0) : d144624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143295, d144624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143295, d144624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143296 q = 0) : d144625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143296, d144625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143296, d144625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143320 q = 0) : d144649 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143320, d144649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143320, d144649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143388 q = 0) : d144692 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143388, d144692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143388, d144692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12499 (p : Pattern) (selected : d143393 p = 0) : d144697 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143285 q = 0) : d144614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12473 q selected
    | true =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143286 q = 0) : d144615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143289 q = 0) : d144618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12474 q selected
    | true =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143290 q = 0) : d144619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143291 q = 0) : d144620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143291, d144620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143291, d144620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143326 q = 0) : d144655 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143326, d144655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143326, d144655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143327 q = 0) : d144656 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143327, d144656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143327, d144656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143393 q = 0) : d144697 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143393, d144697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143393, d144697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
end NetHack.Soko22Hazard87
