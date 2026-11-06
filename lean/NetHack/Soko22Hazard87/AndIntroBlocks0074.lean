import NetHack.Soko22Hazard87.AndIntroBlocks0073
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro18500 (p : Pattern) (ha : d8112 p = 1) (hb : d112688 p = 1) : d114908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8076 q = 1) (hb : d112688 q = 1) : d114881 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8076, d114881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18492 q ha hb
    | true =>
      simp only [d8076, d114881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8077 q = 1) (hb : d112688 q = 1) : d114882 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8077, d114882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8077, d114882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8038 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18481 q ha hb
    | true =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8039 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8078 q = 1) (hb : d112688 q = 1) : d114883 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8078, d114883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8078, d114883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8079 q = 1) (hb : d112688 q = 1) : d114884 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8079, d114884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8079, d114884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8080 q = 1) (hb : d112688 q = 1) : d114885 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8080, d114885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8080, d114885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8112 q = 1) (hb : d112688 q = 1) : d114908 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8112, d114908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8112, d114908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18501 (p : Pattern) (ha : d8117 p = 1) (hb : d112688 p = 1) : d114911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18481 q ha hb
    | true =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8093 q = 1) (hb : d112688 q = 1) : d114889 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8093, d114889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8093, d114889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8094 q = 1) (hb : d112688 q = 1) : d114890 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8094, d114890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8094, d114890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8095 q = 1) (hb : d112688 q = 1) : d114891 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8095, d114891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8095, d114891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8117 q = 1) (hb : d112688 q = 1) : d114911 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8117, d114911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8117, d114911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18502 (p : Pattern) (ha : d85642 p = 1) (hb : d112688 p = 1) : d114917 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8064 q = 1) (hb : d112688 q = 1) : d114865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8064, d114865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18489 q ha hb
    | true =>
      simp only [d8064, d114865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18487 q ha hb
  have h2 (q : Pattern) (ha : d8065 q = 1) (hb : d112688 q = 1) : d114866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8065, d114866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8065, d114866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8066 q = 1) (hb : d112688 q = 1) : d114867 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8066, d114867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8066, d114867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8067 q = 1) (hb : d112688 q = 1) : d114868 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8067, d114868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8067, d114868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8071 q = 1) (hb : d112688 q = 1) : d114872 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8071, d114872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18490 q ha hb
    | true =>
      simp only [d8071, d114872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18488 q ha hb
  have h6 (q : Pattern) (ha : d8072 q = 1) (hb : d112688 q = 1) : d114873 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8072, d114873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8072, d114873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8073 q = 1) (hb : d112688 q = 1) : d114874 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8073, d114874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8073, d114874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8082 q = 1) (hb : d112688 q = 1) : d114887 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8082, d114887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18493 q ha hb
    | true =>
      simp only [d8082, d114887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18482 q ha hb
  have h9 (q : Pattern) (ha : d85633 q = 1) (hb : d112688 q = 1) : d114888 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85633, d114888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85633, d114888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8097 q = 1) (hb : d112688 q = 1) : d114893 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8097, d114893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18494 q ha hb
    | true =>
      simp only [d8097, d114893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8098 q = 1) (hb : d112688 q = 1) : d114894 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8098, d114894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8098, d114894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85634 q = 1) (hb : d112688 q = 1) : d114895 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85634, d114895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85634, d114895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85635 q = 1) (hb : d112688 q = 1) : d114896 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85635, d114896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85635, d114896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85636 q = 1) (hb : d112688 q = 1) : d114897 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85636, d114897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85636, d114897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8104 q = 1) (hb : d112688 q = 1) : d114900 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8104, d114900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18498 q ha hb
    | true =>
      simp only [d8104, d114900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18496 q ha hb
  have h16 (q : Pattern) (ha : d8105 q = 1) (hb : d112688 q = 1) : d114901 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8105, d114901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8105, d114901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8106 q = 1) (hb : d112688 q = 1) : d114902 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8106, d114902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8106, d114902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8107 q = 1) (hb : d112688 q = 1) : d114903 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8107, d114903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8107, d114903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8109 q = 1) (hb : d112688 q = 1) : d114905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8109, d114905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18499 q ha hb
    | true =>
      simp only [d8109, d114905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18497 q ha hb
  have h20 (q : Pattern) (ha : d8110 q = 1) (hb : d112688 q = 1) : d114906 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8110, d114906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8110, d114906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8111 q = 1) (hb : d112688 q = 1) : d114907 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8111, d114907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8111, d114907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8113 q = 1) (hb : d112688 q = 1) : d114909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8113, d114909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18500 q ha hb
    | true =>
      simp only [d8113, d114909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18484 q ha hb
  have h23 (q : Pattern) (ha : d85638 q = 1) (hb : d112688 q = 1) : d114910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85638, d114910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85638, d114910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8118 q = 1) (hb : d112688 q = 1) : d114912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8118, d114912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18501 q ha hb
    | true =>
      simp only [d8118, d114912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8119 q = 1) (hb : d112688 q = 1) : d114913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8119, d114913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8119, d114913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d85639 q = 1) (hb : d112688 q = 1) : d114914 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85639, d114914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d85639, d114914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d85640 q = 1) (hb : d112688 q = 1) : d114915 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85640, d114915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85640, d114915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d85641 q = 1) (hb : d112688 q = 1) : d114916 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85641, d114916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85641, d114916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d85642 q = 1) (hb : d112688 q = 1) : d114917 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85642, d114917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85642, d114917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro18503 (p : Pattern) (ha : d85649 p = 1) (hb : d112688 p = 1) : d114926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8113 q = 1) (hb : d112688 q = 1) : d114909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8113, d114909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18500 q ha hb
    | true =>
      simp only [d8113, d114909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18484 q ha hb
  have h2 (q : Pattern) (ha : d85638 q = 1) (hb : d112688 q = 1) : d114910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85638, d114910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85638, d114910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8118 q = 1) (hb : d112688 q = 1) : d114912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8118, d114912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18501 q ha hb
    | true =>
      simp only [d8118, d114912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8119 q = 1) (hb : d112688 q = 1) : d114913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8119, d114913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8119, d114913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85639 q = 1) (hb : d112688 q = 1) : d114914 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85639, d114914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85639, d114914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85647 q = 1) (hb : d112688 q = 1) : d114924 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85647, d114924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85647, d114924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85648 q = 1) (hb : d112688 q = 1) : d114925 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85648, d114925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85648, d114925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85649 q = 1) (hb : d112688 q = 1) : d114926 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85649, d114926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85649, d114926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18504 (p : Pattern) (ha : d2345 p = 1) (hb : d94753 p = 1) : d13808 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2339 q = 1) : d2339 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2344 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2345 q = 1) (hb : d94753 q = 1) : d13808 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2345, d94753, d13808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2345, d94753, d13808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro18505 (p : Pattern) (ha : d8139 p = 1) (hb : d112688 p = 1) : d114937 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2352 q = 1) (hb : d94753 q = 1) : d13810 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2352, d13810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18504 q ha hb
    | true =>
      simp only [d2352, d13810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12677 q ha hb
  have h2 (q : Pattern) (ha : d2353 q = 1) (hb : d94753 q = 1) : d13811 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2353, d13811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2353, d13811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2354 q = 1) (hb : d94753 q = 1) : d13812 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2354, d13812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2354, d13812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2356 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2357 q = 1) (hb : d112686 q = 1) : d114932 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d112686, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12677 q ha hb
    | true =>
      simp only [d2357, d112686, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d2358 q = 1) (hb : d112686 q = 1) : d114933 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2358, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2359 q = 1) (hb : d112686 q = 1) : d114934 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2359, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2360 q = 1) (hb : d112687 q = 1) : d114935 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2360, d112687, d114935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2360, d112687, d114935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d8138 q = 1) (hb : d112688 q = 1) : d114936 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8138, d112688, d114936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8138, d112688, d114936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8139 q = 1) (hb : d112688 q = 1) : d114937 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8139, d114937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8139, d114937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18506 (p : Pattern) (ha : d8143 p = 1) (hb : d112688 p = 1) : d114942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2357 q = 1) (hb : d94753 q = 1) : d13827 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d13827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12677 q ha hb
    | true =>
      simp only [d2357, d13827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12673 q ha hb
  have h2 (q : Pattern) (ha : d2358 q = 1) (hb : d94753 q = 1) : d13828 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d13828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d13828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2359 q = 1) (hb : d94753 q = 1) : d13829 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d13829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d13829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2366 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2367 q = 1) (hb : d112686 q = 1) : d89012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12673 q ha hb
    | true =>
      simp only [d2367, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d2368 q = 1) (hb : d112686 q = 1) : d89013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2368, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2369 q = 1) (hb : d112686 q = 1) : d89014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2369, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2370 q = 1) (hb : d112687 q = 1) : d114940 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d112687, d114940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2370, d112687, d114940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d8142 q = 1) (hb : d112688 q = 1) : d114941 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8142, d112688, d114941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8142, d112688, d114941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8143 q = 1) (hb : d112688 q = 1) : d114942 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8143, d114942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8143, d114942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18507 (p : Pattern) (ha : d8149 p = 1) (hb : d112688 p = 1) : d114948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8140 q = 1) (hb : d112688 q = 1) : d114938 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8140, d114938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18505 q ha hb
    | true =>
      simp only [d8140, d114938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8141 q = 1) (hb : d112688 q = 1) : d114939 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8141, d114939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8141, d114939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8144 q = 1) (hb : d112688 q = 1) : d114943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8144, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18506 q ha hb
    | true =>
      simp only [d8144, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8145 q = 1) (hb : d112688 q = 1) : d114944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8145, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8145, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8146 q = 1) (hb : d112688 q = 1) : d114945 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8146, d114945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8146, d114945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8147 q = 1) (hb : d112688 q = 1) : d114946 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8147, d114946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8147, d114946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8148 q = 1) (hb : d112688 q = 1) : d114947 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8148, d114947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8148, d114947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8149 q = 1) (hb : d112688 q = 1) : d114948 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8149, d114948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8149, d114948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18508 (p : Pattern) (ha : d8153 p = 1) (hb : d112688 p = 1) : d114952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8144 q = 1) (hb : d112688 q = 1) : d114943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8144, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18506 q ha hb
    | true =>
      simp only [d8144, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8145 q = 1) (hb : d112688 q = 1) : d114944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8145, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8145, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2386 q = 1) (hb : d112688 q = 1) : d13850 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d13850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18478 q ha hb
    | true =>
      simp only [d2386, d13850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d112688 q = 1) : d13851 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d13851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d13851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8150 q = 1) (hb : d112688 q = 1) : d114949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8150, d114949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8150, d114949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8151 q = 1) (hb : d112688 q = 1) : d114950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8151, d114950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8151, d114950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8152 q = 1) (hb : d112688 q = 1) : d114951 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8152, d114951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8152, d114951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8153 q = 1) (hb : d112688 q = 1) : d114952 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8153, d114952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8153, d114952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18509 (p : Pattern) (ha : d8168 p = 1) (hb : d112688 p = 1) : d114958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8144 q = 1) (hb : d112688 q = 1) : d114943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8144, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18506 q ha hb
    | true =>
      simp only [d8144, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8145 q = 1) (hb : d112688 q = 1) : d114944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8145, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8145, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8165 q = 1) (hb : d112688 q = 1) : d114955 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8165, d114955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8165, d114955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8166 q = 1) (hb : d112688 q = 1) : d114956 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8166, d114956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8166, d114956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8167 q = 1) (hb : d112688 q = 1) : d114957 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8167, d114957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8167, d114957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8168 q = 1) (hb : d112688 q = 1) : d114958 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8168, d114958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8168, d114958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18510 (p : Pattern) (ha : d85659 p = 1) (hb : d112688 p = 1) : d114964 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8154 q = 1) (hb : d112688 q = 1) : d114953 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8154, d114953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18507 q ha hb
    | true =>
      simp only [d8154, d114953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18508 q ha hb
  have h2 (q : Pattern) (ha : d85655 q = 1) (hb : d112688 q = 1) : d114954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85655, d114954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85655, d114954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8169 q = 1) (hb : d112688 q = 1) : d114959 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8169, d114959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18509 q ha hb
    | true =>
      simp only [d8169, d114959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8170 q = 1) (hb : d112688 q = 1) : d114960 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8170, d114960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8170, d114960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85656 q = 1) (hb : d112688 q = 1) : d114961 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85656, d114961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85656, d114961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85657 q = 1) (hb : d112688 q = 1) : d114962 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85657, d114962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85657, d114962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85658 q = 1) (hb : d112688 q = 1) : d114963 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85658, d114963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85658, d114963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85659 q = 1) (hb : d112688 q = 1) : d114964 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85659, d114964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85659, d114964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18511 (p : Pattern) (ha : d85665 p = 1) (hb : d112688 p = 1) : d114970 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8050 q = 1) (hb : d112688 q = 1) : d114851 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8050, d114851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8050, d114851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18483 q ha hb
  have h2 (q : Pattern) (ha : d8051 q = 1) (hb : d112688 q = 1) : d114852 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8051, d114852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8051, d114852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8059 q = 1) (hb : d112688 q = 1) : d114860 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8059, d114860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18483 q ha hb
    | true =>
      simp only [d8059, d114860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18485 q ha hb
  have h4 (q : Pattern) (ha : d8060 q = 1) (hb : d112688 q = 1) : d114861 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8060, d114861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8060, d114861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8061 q = 1) (hb : d112688 q = 1) : d114862 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8061, d114862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8061, d114862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85643 q = 1) (hb : d112688 q = 1) : d114918 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85643, d114918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18495 q ha hb
    | true =>
      simp only [d85643, d114918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18502 q ha hb
  have h7 (q : Pattern) (ha : d8126 q = 1) (hb : d112688 q = 1) : d114920 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8126, d114920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18486 q ha hb
    | true =>
      simp only [d8126, d114920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18476 q ha hb
  have h8 (q : Pattern) (ha : d85644 q = 1) (hb : d112688 q = 1) : d114921 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85644, d114921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85644, d114921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85645 q = 1) (hb : d112688 q = 1) : d114922 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85645, d114922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85645, d114922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d85646 q = 1) (hb : d112688 q = 1) : d114923 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85646, d114923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85646, d114923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85650 q = 1) (hb : d112688 q = 1) : d114927 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85650, d114927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85650, d114927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18503 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d112688 q = 1) : d13803 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d13803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, d13803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18477 q ha hb
  have h13 (q : Pattern) (ha : d85651 q = 1) (hb : d112688 q = 1) : d114928 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85651, d114928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85651, d114928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85652 q = 1) (hb : d112688 q = 1) : d114929 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85652, d114929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85652, d114929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d85653 q = 1) (hb : d112688 q = 1) : d114930 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85653, d114930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85653, d114930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d85654 q = 1) (hb : d112688 q = 1) : d114931 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85654, d114931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85654, d114931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85660 q = 1) (hb : d112688 q = 1) : d114965 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85660, d114965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85660, d114965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18510 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d112688 q = 1) : d13920 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, d13920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, d13920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18480 q ha hb
  have h19 (q : Pattern) (ha : d85661 q = 1) (hb : d112688 q = 1) : d114966 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85661, d114966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85661, d114966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d85662 q = 1) (hb : d112688 q = 1) : d114967 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85662, d114967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d85662, d114967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d85663 q = 1) (hb : d112688 q = 1) : d114968 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85663, d114968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85663, d114968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d85664 q = 1) (hb : d112688 q = 1) : d114969 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85664, d114969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85664, d114969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d85665 q = 1) (hb : d112688 q = 1) : d114970 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85665, d114970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85665, d114970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro18512 (p : Pattern) (ha : d85671 p = 1) (hb : d112688 p = 1) : d114976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85666 q = 1) (hb : d112688 q = 1) : d114971 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85666, d114971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85666, d114971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18511 q ha hb
  have h2 (q : Pattern) (ha : d85667 q = 1) (hb : d112688 q = 1) : d114972 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85667, d114972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85667, d114972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85668 q = 1) (hb : d112688 q = 1) : d114973 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85668, d114973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85668, d114973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85669 q = 1) (hb : d112688 q = 1) : d114974 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85669, d114974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85669, d114974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85670 q = 1) (hb : d112688 q = 1) : d114975 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85670, d114975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85670, d114975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85671 q = 1) (hb : d112688 q = 1) : d114976 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85671, d114976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85671, d114976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18513 (p : Pattern) (ha : d85677 p = 1) (hb : d112688 p = 1) : d114982 p = 1 := by
  have h0 (q : Pattern) (ha : d85506 q = 1) (hb : d112688 q = 1) : d114403 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85506, d114403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18314 q ha hb
    | true =>
      simp only [d85506, d114403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18352 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d85546 q = 1) (hb : d112688 q = 1) : d114545 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85546, d114545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85546, d114545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18392 q ha hb
  have h3 (q : Pattern) (ha : d85547 q = 1) (hb : d112688 q = 1) : d114546 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85547, d114546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85547, d114546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85587 q = 1) (hb : d112688 q = 1) : d114688 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85587, d114688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85587, d114688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18432 q ha hb
  have h5 (q : Pattern) (ha : d85588 q = 1) (hb : d112688 q = 1) : d114689 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85588, d114689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85588, d114689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85589 q = 1) (hb : d112688 q = 1) : d114690 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85589, d114690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85589, d114690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85629 q = 1) (hb : d112688 q = 1) : d114832 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85629, d114832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85629, d114832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18472 q ha hb
  have h8 (q : Pattern) (ha : d85630 q = 1) (hb : d112688 q = 1) : d114833 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85630, d114833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85630, d114833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85631 q = 1) (hb : d112688 q = 1) : d114834 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85631, d114834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85631, d114834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85632 q = 1) (hb : d112688 q = 1) : d114835 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85632, d114835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85632, d114835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85672 q = 1) (hb : d112688 q = 1) : d114977 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85672, d114977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85672, d114977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18512 q ha hb
  have h12 (q : Pattern) (ha : d85673 q = 1) (hb : d112688 q = 1) : d114978 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85673, d114978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85673, d114978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85674 q = 1) (hb : d112688 q = 1) : d114979 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85674, d114979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85674, d114979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85675 q = 1) (hb : d112688 q = 1) : d114980 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85675, d114980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85675, d114980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85676 q = 1) (hb : d112688 q = 1) : d114981 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d85676, d114981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85676, d114981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85677 q = 1) (hb : d112688 q = 1) : d114982 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d85677, d114982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85677, d114982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro18514 (p : Pattern) (ha : d85683 p = 1) (hb : d112688 p = 1) : d114988 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85678 q = 1) (hb : d112688 q = 1) : d114983 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d85678, d114983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18513 q ha hb
    | true =>
      simp only [d85678, d114983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85679 q = 1) (hb : d112688 q = 1) : d114984 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d85679, d114984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85679, d114984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85680 q = 1) (hb : d112688 q = 1) : d114985 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d85680, d114985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85680, d114985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85681 q = 1) (hb : d112688 q = 1) : d114986 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d85681, d114986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85681, d114986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85682 q = 1) (hb : d112688 q = 1) : d114987 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d85682, d114987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85682, d114987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85683 q = 1) (hb : d112688 q = 1) : d114988 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d85683, d114988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85683, d114988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18515 (p : Pattern) (ha : d85689 p = 1) (hb : d112688 p = 1) : d114994 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85684 q = 1) (hb : d112688 q = 1) : d114989 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d85684, d114989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18514 q ha hb
    | true =>
      simp only [d85684, d114989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85685 q = 1) (hb : d112688 q = 1) : d114990 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d85685, d114990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85685, d114990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85686 q = 1) (hb : d112688 q = 1) : d114991 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d85686, d114991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85686, d114991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85687 q = 1) (hb : d112688 q = 1) : d114992 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d85687, d114992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85687, d114992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85688 q = 1) (hb : d112688 q = 1) : d114993 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d85688, d114993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85688, d114993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85689 q = 1) (hb : d112688 q = 1) : d114994 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d85689, d114994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85689, d114994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18516 (p : Pattern) (ha : d85695 p = 1) (hb : d112688 p = 1) : d115000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85690 q = 1) (hb : d112688 q = 1) : d114995 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d85690, d114995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18515 q ha hb
    | true =>
      simp only [d85690, d114995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85691 q = 1) (hb : d112688 q = 1) : d114996 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d85691, d114996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85691, d114996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85692 q = 1) (hb : d112688 q = 1) : d114997 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d85692, d114997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85692, d114997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85693 q = 1) (hb : d112688 q = 1) : d114998 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d85693, d114998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85693, d114998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85694 q = 1) (hb : d112688 q = 1) : d114999 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d85694, d114999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85694, d114999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85695 q = 1) (hb : d112688 q = 1) : d115000 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d85695, d115000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85695, d115000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18517 (p : Pattern) (ha : d85701 p = 1) (hb : d112688 p = 1) : d115006 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85696 q = 1) (hb : d112688 q = 1) : d115001 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d85696, d115001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18516 q ha hb
    | true =>
      simp only [d85696, d115001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85697 q = 1) (hb : d112688 q = 1) : d115002 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d85697, d115002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85697, d115002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85698 q = 1) (hb : d112688 q = 1) : d115003 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d85698, d115003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85698, d115003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85699 q = 1) (hb : d112688 q = 1) : d115004 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d85699, d115004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85699, d115004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85700 q = 1) (hb : d112688 q = 1) : d115005 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d85700, d115005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85700, d115005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85701 q = 1) (hb : d112688 q = 1) : d115006 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d85701, d115006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85701, d115006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18518 (p : Pattern) (ha : d85707 p = 1) (hb : d112688 p = 1) : d115012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85702 q = 1) (hb : d112688 q = 1) : d115007 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d85702, d115007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18517 q ha hb
    | true =>
      simp only [d85702, d115007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85703 q = 1) (hb : d112688 q = 1) : d115008 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d85703, d115008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85703, d115008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85704 q = 1) (hb : d112688 q = 1) : d115009 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d85704, d115009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85704, d115009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85705 q = 1) (hb : d112688 q = 1) : d115010 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d85705, d115010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85705, d115010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85706 q = 1) (hb : d112688 q = 1) : d115011 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d85706, d115011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85706, d115011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85707 q = 1) (hb : d112688 q = 1) : d115012 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d85707, d115012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85707, d115012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18519 (p : Pattern) (ha : d85713 p = 1) (hb : d112688 p = 1) : d115018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85708 q = 1) (hb : d112688 q = 1) : d115013 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d85708, d115013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18518 q ha hb
    | true =>
      simp only [d85708, d115013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85709 q = 1) (hb : d112688 q = 1) : d115014 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d85709, d115014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85709, d115014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85710 q = 1) (hb : d112688 q = 1) : d115015 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d85710, d115015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85710, d115015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85711 q = 1) (hb : d112688 q = 1) : d115016 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d85711, d115016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85711, d115016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85712 q = 1) (hb : d112688 q = 1) : d115017 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d85712, d115017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85712, d115017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85713 q = 1) (hb : d112688 q = 1) : d115018 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d85713, d115018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85713, d115018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18520 (p : Pattern) (ha : d85719 p = 1) (hb : d112688 p = 1) : d115024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85714 q = 1) (hb : d112688 q = 1) : d115019 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d85714, d115019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18519 q ha hb
    | true =>
      simp only [d85714, d115019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85715 q = 1) (hb : d112688 q = 1) : d115020 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d85715, d115020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85715, d115020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85716 q = 1) (hb : d112688 q = 1) : d115021 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d85716, d115021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85716, d115021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85717 q = 1) (hb : d112688 q = 1) : d115022 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d85717, d115022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85717, d115022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85718 q = 1) (hb : d112688 q = 1) : d115023 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d85718, d115023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85718, d115023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85719 q = 1) (hb : d112688 q = 1) : d115024 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d85719, d115024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85719, d115024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18521 (p : Pattern) (ha : d112691 p = 1) (hb : d114101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4819 q = 1) (hb : d68915 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d68915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7917 q ha hb
    | true =>
      simp only [d4819, d68915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h2 (q : Pattern) (ha : d4820 q = 1) (hb : d68916 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d68916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d68916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4821 q = 1) (hb : d68917 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d68917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d68917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h7 (q : Pattern) (ha : d12225 q = 1) (hb : d112689 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12225, d112689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12225, d112689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d112690 q = 1) (hb : d114100 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d112690, d114100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d112690, d114100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d112691 q = 1) (hb : d114101 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d112691, d114101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d112691, d114101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro18522 (p : Pattern) (ha : d112697 p = 1) (hb : d114107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112692 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18521 q ha hb
    | true =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112693 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d112694 q = 1) (hb : d114104 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112694, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112694, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112695 q = 1) (hb : d114105 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112695, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112695, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112696 q = 1) (hb : d114106 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112696, d114106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112696, d114106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112697 q = 1) (hb : d114107 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112697, d114107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112697, d114107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18523 (p : Pattern) (ha : d112703 p = 1) (hb : d114113 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d112698 q = 1) (hb : d114108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112698, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18522 q ha hb
    | true =>
      simp only [d112698, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112699 q = 1) (hb : d114109 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112699, d114109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112699, d114109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d112700 q = 1) (hb : d114110 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112700, d114110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112700, d114110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d112701 q = 1) (hb : d114111 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112701, d114111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d112701, d114111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112702 q = 1) (hb : d114112 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112702, d114112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112702, d114112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112703 q = 1) (hb : d114113 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112703, d114113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112703, d114113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro18524 (p : Pattern) (ha : d112704 p = 1) (hb : d114114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112692 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18521 q ha hb
    | true =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112693 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d112694 q = 1) (hb : d114104 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112694, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112694, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112695 q = 1) (hb : d114105 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112695, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112695, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112696 q = 1) (hb : d114106 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112696, d114106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112696, d114106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112704 q = 1) (hb : d114114 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112704, d114114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112704, d114114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18525 (p : Pattern) (ha : d112710 p = 1) (hb : d114120 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d112698 q = 1) (hb : d114108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112698, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18522 q ha hb
    | true =>
      simp only [d112698, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112699 q = 1) (hb : d114109 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112699, d114109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112699, d114109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d112700 q = 1) (hb : d114110 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112700, d114110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112700, d114110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d112701 q = 1) (hb : d114111 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112701, d114111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d112701, d114111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112702 q = 1) (hb : d114112 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112702, d114112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112702, d114112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h23 (q : Pattern) (ha : d112705 q = 1) (hb : d114115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112705, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18524 q ha hb
    | true =>
      simp only [d112705, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d112706 q = 1) (hb : d114116 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112706, d114116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d112706, d114116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h28 (q : Pattern) (ha : d112707 q = 1) (hb : d114117 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112707, d114117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d112707, d114117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d112708 q = 1) (hb : d114118 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112708, d114118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d112708, d114118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d112709 q = 1) (hb : d114119 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112709, d114119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d112709, d114119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d112710 q = 1) (hb : d114120 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112710, d114120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d112710, d114120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro18526 (p : Pattern) (ha : d112717 p = 1) (hb : d114127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112705 q = 1) (hb : d114115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112705, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18524 q ha hb
    | true =>
      simp only [d112705, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112706 q = 1) (hb : d114116 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112706, d114116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112706, d114116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d112707 q = 1) (hb : d114117 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112707, d114117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112707, d114117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d112715 q = 1) (hb : d114125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112715, d114125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112715, d114125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112716 q = 1) (hb : d114126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112716, d114126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112716, d114126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112717 q = 1) (hb : d114127 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112717, d114127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112717, d114127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro18527 (p : Pattern) (ha : d112725 p = 1) (hb : d114134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6079 q = 1) (hb : d75841 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d75841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q ha hb
    | true =>
      simp only [d6079, d75841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h2 (q : Pattern) (ha : d6080 q = 1) (hb : d75842 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d75842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d75842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6081 q = 1) (hb : d75843 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d75843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d75843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h7 (q : Pattern) (ha : d12259 q = 1) (hb : d112723 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12259, d112723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12259, d112723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d112724 q = 1) (hb : d114133 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d112724, d114133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d112724, d114133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d112725 q = 1) (hb : d114134 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d112725, d114134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d112725, d114134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro18528 (p : Pattern) (ha : d112731 p = 1) (hb : d114140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112726 q = 1) (hb : d114135 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112726, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18527 q ha hb
    | true =>
      simp only [d112726, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112727 q = 1) (hb : d114136 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112727, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112727, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d112728 q = 1) (hb : d114137 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112728, d114137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112728, d114137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112729 q = 1) (hb : d114138 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112729, d114138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112729, d114138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112730 q = 1) (hb : d114139 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112730, d114139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112730, d114139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112731 q = 1) (hb : d114140 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112731, d114140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112731, d114140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18529 (p : Pattern) (ha : d112737 p = 1) (hb : d114146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112732 q = 1) (hb : d114141 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112732, d114141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18528 q ha hb
    | true =>
      simp only [d112732, d114141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112733 q = 1) (hb : d114142 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112733, d114142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112733, d114142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d112734 q = 1) (hb : d114143 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112734, d114143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112734, d114143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d112735 q = 1) (hb : d114144 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112735, d114144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112735, d114144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112736 q = 1) (hb : d114145 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112736, d114145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112736, d114145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112737 q = 1) (hb : d114146 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112737, d114146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112737, d114146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro18530 (p : Pattern) (ha : d112743 p = 1) (hb : d114152 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d112711 q = 1) (hb : d114121 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112711, d114121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18523 q ha hb
    | true =>
      simp only [d112711, d114121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18525 q ha hb
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
  have h8 (q : Pattern) (ha : d112712 q = 1) (hb : d114122 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112712, d114122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112712, d114122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d112713 q = 1) (hb : d114123 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112713, d114123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112713, d114123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d112714 q = 1) (hb : d114124 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112714, d114124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d112714, d114124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112718 q = 1) (hb : d114128 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112718, d114128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112718, d114128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18526 q ha hb
  have h12 (q : Pattern) (ha : d112719 q = 1) (hb : d114129 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112719, d114129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112719, d114129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112720 q = 1) (hb : d114130 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112720, d114130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d112720, d114130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d112721 q = 1) (hb : d114131 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112721, d114131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d112721, d114131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d112722 q = 1) (hb : d114132 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d112722, d114132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112722, d114132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112738 q = 1) (hb : d114147 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112738, d114147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112738, d114147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18529 q ha hb
  have h17 (q : Pattern) (ha : d112739 q = 1) (hb : d114148 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112739, d114148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d112739, d114148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d112740 q = 1) (hb : d114149 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112740, d114149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d112740, d114149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d112741 q = 1) (hb : d114150 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112741, d114150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d112741, d114150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d112742 q = 1) (hb : d114151 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d112742, d114151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d112742, d114151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d112743 q = 1) (hb : d114152 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d112743, d114152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d112743, d114152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro18531 (p : Pattern) (ha : d112753 p = 1) (hb : d114162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112698 q = 1) (hb : d114108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112698, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18522 q ha hb
    | true =>
      simp only [d112698, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d112749 q = 1) (hb : d114158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112749, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112749, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112750 q = 1) (hb : d114159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112750, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112750, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112751 q = 1) (hb : d114160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112751, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112751, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112752 q = 1) (hb : d114161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112752, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112752, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112753 q = 1) (hb : d114162 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112753, d114162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112753, d114162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18532 (p : Pattern) (ha : d112760 p = 1) (hb : d114169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112698 q = 1) (hb : d114108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112698, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18522 q ha hb
    | true =>
      simp only [d112698, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d112749 q = 1) (hb : d114158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112749, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112749, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112750 q = 1) (hb : d114159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112750, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112750, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112751 q = 1) (hb : d114160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112751, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112751, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112752 q = 1) (hb : d114161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112752, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112752, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112705 q = 1) (hb : d114115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112705, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18524 q ha hb
    | true =>
      simp only [d112705, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d112756 q = 1) (hb : d114165 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112756, d114165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112756, d114165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112757 q = 1) (hb : d114166 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112757, d114166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112757, d114166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d112758 q = 1) (hb : d114167 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112758, d114167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112758, d114167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112759 q = 1) (hb : d114168 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112759, d114168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112759, d114168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112760 q = 1) (hb : d114169 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112760, d114169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112760, d114169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18533 (p : Pattern) (ha : d112765 p = 1) (hb : d114174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112692 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18521 q ha hb
    | true =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112693 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d112694 q = 1) (hb : d114104 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112694, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112694, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112695 q = 1) (hb : d114105 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112695, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112695, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112764 q = 1) (hb : d114173 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112764, d114173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112764, d114173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112765 q = 1) (hb : d114174 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112765, d114174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112765, d114174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18534 (p : Pattern) (ha : d112772 p = 1) (hb : d114181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112692 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18521 q ha hb
    | true =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112693 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d112694 q = 1) (hb : d114104 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112694, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112694, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112770 q = 1) (hb : d114179 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112770, d114179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112770, d114179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112771 q = 1) (hb : d114180 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112771, d114180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112771, d114180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112772 q = 1) (hb : d114181 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112772, d114181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112772, d114181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18535 (p : Pattern) (ha : d12312 p = 1) (hb : d112776 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d141 q = 1) (hb : d51992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d142 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d323 q = 1) (hb : d52122 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d323, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12312 q = 1) (hb : d112776 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12312, d112776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12312, d112776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro18536 (p : Pattern) (ha : d112782 p = 1) (hb : d114187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12313 q = 1) (hb : d112777 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d112777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18535 q ha hb
    | true =>
      simp only [d12313, d112777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7917 q ha hb
  have h2 (q : Pattern) (ha : d12314 q = 1) (hb : d112778 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d112778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d112778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12315 q = 1) (hb : d112779 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d112779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d112779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d68915 q = 1) (hb : d88338 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d68915, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7917 q hb ha
    | true =>
      simp only [d68915, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d68916 q = 1) (hb : d88339 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d68916, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68916, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68917 q = 1) (hb : d88340 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d68917, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68917, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112780 q = 1) (hb : d114185 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112780, d114185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d112780, d114185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112689 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112781 q = 1) (hb : d114186 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d112781, d114186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112781, d114186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d112782 q = 1) (hb : d114187 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d112782, d114187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112782, d114187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18537 (p : Pattern) (ha : d112788 p = 1) (hb : d114193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112783 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112783, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18536 q ha hb
    | true =>
      simp only [d112783, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112784 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112784, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112784, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112692 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18521 q ha hb
    | true =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112693 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112785 q = 1) (hb : d114190 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112785, d114190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112785, d114190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112786 q = 1) (hb : d114191 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112786, d114191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112786, d114191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112787 q = 1) (hb : d114192 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112787, d114192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112787, d114192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112788 q = 1) (hb : d114193 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112788, d114193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112788, d114193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18538 (p : Pattern) (ha : d112794 p = 1) (hb : d114199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112692 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18521 q ha hb
    | true =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112693 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112791 q = 1) (hb : d114196 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112791, d114196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112791, d114196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112792 q = 1) (hb : d114197 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112792, d114197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112792, d114197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112793 q = 1) (hb : d114198 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112793, d114198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112793, d114198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112794 q = 1) (hb : d114199 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112794, d114199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112794, d114199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18539 (p : Pattern) (ha : d112800 p = 1) (hb : d114205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112766 q = 1) (hb : d114175 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112766, d114175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18533 q ha hb
    | true =>
      simp only [d112766, d114175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d112767 q = 1) (hb : d114176 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112767, d114176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112767, d114176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112768 q = 1) (hb : d114177 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112768, d114177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112768, d114177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112769 q = 1) (hb : d114178 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112769, d114178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112769, d114178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112773 q = 1) (hb : d114182 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112773, d114182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18534 q ha hb
    | true =>
      simp only [d112773, d114182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d112774 q = 1) (hb : d114183 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112774, d114183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112774, d114183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112775 q = 1) (hb : d114184 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112775, d114184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112775, d114184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112789 q = 1) (hb : d114194 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112789, d114194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18537 q ha hb
    | true =>
      simp only [d112789, d114194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18522 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112698 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112790 q = 1) (hb : d114195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112790, d114195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112790, d114195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d112795 q = 1) (hb : d114200 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112795, d114200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18538 q ha hb
    | true =>
      simp only [d112795, d114200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112796 q = 1) (hb : d114201 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112796, d114201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112796, d114201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112797 q = 1) (hb : d114202 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112797, d114202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112797, d114202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d112798 q = 1) (hb : d114203 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112798, d114203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112798, d114203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112799 q = 1) (hb : d114204 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112799, d114204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112799, d114204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112800 q = 1) (hb : d114205 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112800, d114205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112800, d114205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro18540 (p : Pattern) (ha : d112801 p = 1) (hb : d114206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112692 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18521 q ha hb
    | true =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112693 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d112694 q = 1) (hb : d114104 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112694, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112694, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112695 q = 1) (hb : d114105 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112695, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112695, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112764 q = 1) (hb : d114173 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112764, d114173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112764, d114173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112801 q = 1) (hb : d114206 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112801, d114206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112801, d114206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18541 (p : Pattern) (ha : d112806 p = 1) (hb : d114211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112692 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18521 q ha hb
    | true =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112693 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d112694 q = 1) (hb : d114104 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112694, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112694, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112770 q = 1) (hb : d114179 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112770, d114179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112770, d114179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112771 q = 1) (hb : d114180 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112771, d114180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112771, d114180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112806 q = 1) (hb : d114211 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112806, d114211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112806, d114211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18542 (p : Pattern) (ha : d112810 p = 1) (hb : d114215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112783 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112783, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18536 q ha hb
    | true =>
      simp only [d112783, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112784 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112784, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112784, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112692 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18521 q ha hb
    | true =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112693 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112785 q = 1) (hb : d114190 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112785, d114190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112785, d114190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112786 q = 1) (hb : d114191 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112786, d114191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112786, d114191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112787 q = 1) (hb : d114192 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112787, d114192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112787, d114192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112810 q = 1) (hb : d114215 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112810, d114215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112810, d114215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18543 (p : Pattern) (ha : d112813 p = 1) (hb : d114218 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112692 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18521 q ha hb
    | true =>
      simp only [d112692, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112693 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112791 q = 1) (hb : d114196 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112791, d114196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112791, d114196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112792 q = 1) (hb : d114197 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112792, d114197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112792, d114197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112793 q = 1) (hb : d114198 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112793, d114198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112793, d114198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112813 q = 1) (hb : d114218 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112813, d114218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112813, d114218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro18544 (p : Pattern) (ha : d112819 p = 1) (hb : d114224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112766 q = 1) (hb : d114175 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112766, d114175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18533 q ha hb
    | true =>
      simp only [d112766, d114175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d112767 q = 1) (hb : d114176 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112767, d114176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112767, d114176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112768 q = 1) (hb : d114177 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112768, d114177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112768, d114177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112769 q = 1) (hb : d114178 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112769, d114178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112769, d114178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112773 q = 1) (hb : d114182 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112773, d114182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18534 q ha hb
    | true =>
      simp only [d112773, d114182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d112774 q = 1) (hb : d114183 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112774, d114183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112774, d114183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112775 q = 1) (hb : d114184 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112775, d114184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112775, d114184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112789 q = 1) (hb : d114194 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112789, d114194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18537 q ha hb
    | true =>
      simp only [d112789, d114194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18522 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112698 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112790 q = 1) (hb : d114195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112790, d114195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112790, d114195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d112795 q = 1) (hb : d114200 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112795, d114200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18538 q ha hb
    | true =>
      simp only [d112795, d114200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112796 q = 1) (hb : d114201 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112796, d114201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112796, d114201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112797 q = 1) (hb : d114202 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112797, d114202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112797, d114202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d112798 q = 1) (hb : d114203 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112798, d114203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112798, d114203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112799 q = 1) (hb : d114204 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112799, d114204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112799, d114204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112802 q = 1) (hb : d114207 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112802, d114207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18540 q ha hb
    | true =>
      simp only [d112802, d114207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d112803 q = 1) (hb : d114208 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112803, d114208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112803, d114208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d112804 q = 1) (hb : d114209 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112804, d114209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d112804, d114209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d112805 q = 1) (hb : d114210 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112805, d114210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112805, d114210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d112807 q = 1) (hb : d114212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112807, d114212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18541 q ha hb
    | true =>
      simp only [d112807, d114212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d112808 q = 1) (hb : d114213 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112808, d114213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112808, d114213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d112809 q = 1) (hb : d114214 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112809, d114214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d112809, d114214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d112811 q = 1) (hb : d114216 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112811, d114216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18542 q ha hb
    | true =>
      simp only [d112811, d114216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18524 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d112705 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d112812 q = 1) (hb : d114217 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112812, d114217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d112812, d114217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d112814 q = 1) (hb : d114219 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112814, d114219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18543 q ha hb
    | true =>
      simp only [d112814, d114219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d112815 q = 1) (hb : d114220 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112815, d114220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d112815, d114220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d112816 q = 1) (hb : d114221 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112816, d114221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d112816, d114221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d112817 q = 1) (hb : d114222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112817, d114222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d112817, d114222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d112818 q = 1) (hb : d114223 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112818, d114223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d112818, d114223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d112819 q = 1) (hb : d114224 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112819, d114224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d112819, d114224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro18545 (p : Pattern) (ha : d112821 p = 1) (hb : d114226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112698 q = 1) (hb : d114108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112698, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18522 q ha hb
    | true =>
      simp only [d112698, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d112749 q = 1) (hb : d114158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112749, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112749, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112750 q = 1) (hb : d114159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112750, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112750, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112751 q = 1) (hb : d114160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112751, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112751, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112752 q = 1) (hb : d114161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112752, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112752, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d112821 q = 1) (hb : d114226 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112821, d114226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112821, d114226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro18546 (p : Pattern) (ha : d112828 p = 1) (hb : d114233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112811 q = 1) (hb : d114216 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112811, d114216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18542 q ha hb
    | true =>
      simp only [d112811, d114216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18524 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112705 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112812 q = 1) (hb : d114217 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112812, d114217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112812, d114217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d112814 q = 1) (hb : d114219 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112814, d114219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18543 q ha hb
    | true =>
      simp only [d112814, d114219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112815 q = 1) (hb : d114220 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112815, d114220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112815, d114220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112816 q = 1) (hb : d114221 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112816, d114221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112816, d114221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112826 q = 1) (hb : d114231 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112826, d114231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112826, d114231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112827 q = 1) (hb : d114232 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112827, d114232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112827, d114232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112828 q = 1) (hb : d114233 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112828, d114233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112828, d114233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro18547 (p : Pattern) (ha : d12386 p = 1) (hb : d112834 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d226 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
  have h8 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d227 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d228 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d229 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d416 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d416, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12386 q = 1) (hb : d112834 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12386, d112834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12386, d112834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro18548 (p : Pattern) (ha : d112840 p = 1) (hb : d114241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12387 q = 1) (hb : d112835 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d112835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18547 q ha hb
    | true =>
      simp only [d12387, d112835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q ha hb
  have h2 (q : Pattern) (ha : d12388 q = 1) (hb : d112836 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d112836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d112836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12389 q = 1) (hb : d112837 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d112837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d112837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75841 q = 1) (hb : d88402 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d75841, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q hb ha
    | true =>
      simp only [d75841, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75842 q = 1) (hb : d88403 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d75842, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75842, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75843 q = 1) (hb : d88404 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d75843, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75843, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112838 q = 1) (hb : d114239 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112838, d114239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d112838, d114239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112839 q = 1) (hb : d114240 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d112839, d114240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112839, d114240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d112840 q = 1) (hb : d114241 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d112840, d114241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112840, d114241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18549 (p : Pattern) (ha : d112846 p = 1) (hb : d114247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112841 q = 1) (hb : d114242 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112841, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18548 q ha hb
    | true =>
      simp only [d112841, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112842 q = 1) (hb : d114243 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112842, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112842, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112726 q = 1) (hb : d114135 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112726, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18527 q ha hb
    | true =>
      simp only [d112726, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112727 q = 1) (hb : d114136 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112727, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112727, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112843 q = 1) (hb : d114244 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112843, d114244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112843, d114244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112844 q = 1) (hb : d114245 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112844, d114245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112844, d114245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112845 q = 1) (hb : d114246 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112845, d114246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112845, d114246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112846 q = 1) (hb : d114247 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112846, d114247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112846, d114247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18550 (p : Pattern) (ha : d112852 p = 1) (hb : d114253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112726 q = 1) (hb : d114135 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112726, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18527 q ha hb
    | true =>
      simp only [d112726, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112727 q = 1) (hb : d114136 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112727, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112727, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112849 q = 1) (hb : d114250 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112849, d114250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112849, d114250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112850 q = 1) (hb : d114251 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112850, d114251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112850, d114251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112851 q = 1) (hb : d114252 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112851, d114252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112851, d114252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112852 q = 1) (hb : d114253 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112852, d114253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112852, d114253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro18551 (p : Pattern) (ha : d112858 p = 1) (hb : d114259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112847 q = 1) (hb : d114248 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112847, d114248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18549 q ha hb
    | true =>
      simp only [d112847, d114248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18528 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112732 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112848 q = 1) (hb : d114249 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112848, d114249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112848, d114249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d112853 q = 1) (hb : d114254 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112853, d114254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18550 q ha hb
    | true =>
      simp only [d112853, d114254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112854 q = 1) (hb : d114255 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112854, d114255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112854, d114255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112855 q = 1) (hb : d114256 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112855, d114256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112855, d114256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112856 q = 1) (hb : d114257 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112856, d114257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112856, d114257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112857 q = 1) (hb : d114258 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112857, d114258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112857, d114258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112858 q = 1) (hb : d114259 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112858, d114259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112858, d114259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro18552 (p : Pattern) (ha : d112864 p = 1) (hb : d114265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112754 q = 1) (hb : d114163 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112754, d114163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112754, d114163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18531 q ha hb
  have h2 (q : Pattern) (ha : d112755 q = 1) (hb : d114164 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112755, d114164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112755, d114164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112761 q = 1) (hb : d114170 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112761, d114170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18531 q ha hb
    | true =>
      simp only [d112761, d114170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18532 q ha hb
  have h4 (q : Pattern) (ha : d112762 q = 1) (hb : d114171 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112762, d114171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112762, d114171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112763 q = 1) (hb : d114172 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112763, d114172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112763, d114172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112820 q = 1) (hb : d114225 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112820, d114225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18539 q ha hb
    | true =>
      simp only [d112820, d114225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18544 q ha hb
  have h7 (q : Pattern) (ha : d112822 q = 1) (hb : d114227 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112822, d114227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18545 q ha hb
    | true =>
      simp only [d112822, d114227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q hb ha
  have h8 (q : Pattern) (ha : d112823 q = 1) (hb : d114228 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112823, d114228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112823, d114228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112824 q = 1) (hb : d114229 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112824, d114229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112824, d114229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d112825 q = 1) (hb : d114230 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112825, d114230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112825, d114230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112829 q = 1) (hb : d114234 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112829, d114234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112829, d114234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18546 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39 q ha hb
  have h13 (q : Pattern) (ha : d112830 q = 1) (hb : d114235 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112830, d114235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112830, d114235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d112831 q = 1) (hb : d114236 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112831, d114236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d112831, d114236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d112832 q = 1) (hb : d114237 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112832, d114237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d112832, d114237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d112833 q = 1) (hb : d114238 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d112833, d114238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112833, d114238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d112859 q = 1) (hb : d114260 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112859, d114260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112859, d114260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18551 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40 q ha hb
  have h19 (q : Pattern) (ha : d112860 q = 1) (hb : d114261 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112860, d114261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d112860, d114261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d112861 q = 1) (hb : d114262 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112861, d114262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d112861, d114262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d112862 q = 1) (hb : d114263 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112862, d114263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d112862, d114263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d112863 q = 1) (hb : d114264 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d112863, d114264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d112863, d114264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d112864 q = 1) (hb : d114265 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d112864, d114265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d112864, d114265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro18553 (p : Pattern) (ha : d112870 p = 1) (hb : d114271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d51948 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d51949 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d51950 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112744 q = 1) (hb : d114153 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d112744, d114153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112744, d114153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18530 q ha hb
  have h6 (q : Pattern) (ha : d112745 q = 1) (hb : d114154 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d112745, d114154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112745, d114154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112746 q = 1) (hb : d114155 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d112746, d114155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112746, d114155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112747 q = 1) (hb : d114156 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d112747, d114156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112747, d114156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112748 q = 1) (hb : d114157 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d112748, d114157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112748, d114157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112865 q = 1) (hb : d114266 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d112865, d114266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112865, d114266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18552 q ha hb
  have h11 (q : Pattern) (ha : d112866 q = 1) (hb : d114267 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d112866, d114267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112866, d114267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d112867 q = 1) (hb : d114268 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d112867, d114268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112867, d114268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d112868 q = 1) (hb : d114269 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d112868, d114269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112868, d114269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d112869 q = 1) (hb : d114270 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d112869, d114270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112869, d114270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112870 q = 1) (hb : d114271 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d112870, d114271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d112870, d114271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro18554 (p : Pattern) (ha : d12442 p = 1) (hb : d112876 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4819 q = 1) (hb : d68915 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d68915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7917 q ha hb
    | true =>
      simp only [d4819, d68915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h2 (q : Pattern) (ha : d4820 q = 1) (hb : d68916 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d68916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d68916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4821 q = 1) (hb : d68917 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d68917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d68917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4822 q = 1) (hb : d68918 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d68918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4822, d68918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12441 q = 1) (hb : d112875 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12441, d112875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12441, d112875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12442 q = 1) (hb : d112876 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12442, d112876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12442, d112876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18555 (p : Pattern) (ha : d12452 p = 1) (hb : d112886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d112877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18554 q ha hb
    | true =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d112878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d112883 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d112883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d112883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d112884 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d112884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d112884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12451 q = 1) (hb : d112885 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12451, d112885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12451, d112885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12452 q = 1) (hb : d112886 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12452, d112886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12452, d112886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18556 (p : Pattern) (ha : d12462 p = 1) (hb : d112896 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d112877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18554 q ha hb
    | true =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d112878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d112883 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d112883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d112883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d112884 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d112884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d112884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12451 q = 1) (hb : d112885 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12451, d112885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12451, d112885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12462 q = 1) (hb : d112896 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12462, d112896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12462, d112896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18557 (p : Pattern) (ha : d12580 p = 1) (hb : d112988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12569 q = 1) (hb : d112977 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12569, d112977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18555 q ha hb
    | true =>
      simp only [d12569, d112977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12570 q = 1) (hb : d112978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12570, d112978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12570, d112978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12571 q = 1) (hb : d112979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12571, d112979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12571, d112979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12572 q = 1) (hb : d112980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12572, d112980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12572, d112980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12573 q = 1) (hb : d112981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12573, d112981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12573, d112981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12575 q = 1) (hb : d112983 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12575, d112983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18556 q ha hb
    | true =>
      simp only [d12575, d112983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12576 q = 1) (hb : d112984 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12576, d112984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12576, d112984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12577 q = 1) (hb : d112985 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12577, d112985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12577, d112985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12578 q = 1) (hb : d112986 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12578, d112986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12578, d112986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12579 q = 1) (hb : d112987 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12579, d112987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12579, d112987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12580 q = 1) (hb : d112988 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12580, d112988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12580, d112988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18558 (p : Pattern) (ha : d12589 p = 1) (hb : d112997 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12575 q = 1) (hb : d112983 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12575, d112983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18556 q ha hb
    | true =>
      simp only [d12575, d112983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12576 q = 1) (hb : d112984 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12576, d112984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12576, d112984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12577 q = 1) (hb : d112985 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12577, d112985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12577, d112985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12578 q = 1) (hb : d112986 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12578, d112986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12578, d112986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12579 q = 1) (hb : d112987 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12579, d112987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12579, d112987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12589 q = 1) (hb : d112997 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12589, d112997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12589, d112997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18559 (p : Pattern) (ha : d12622 p = 1) (hb : d113030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6079 q = 1) (hb : d75841 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d75841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q ha hb
    | true =>
      simp only [d6079, d75841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h2 (q : Pattern) (ha : d6080 q = 1) (hb : d75842 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d75842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d75842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6081 q = 1) (hb : d75843 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d75843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d75843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6082 q = 1) (hb : d75844 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d75844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6082, d75844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12621 q = 1) (hb : d113029 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12621, d113029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12621, d113029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12622 q = 1) (hb : d113030 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12622, d113030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12622, d113030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18560 (p : Pattern) (ha : d12668 p = 1) (hb : d113041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12623 q = 1) (hb : d113031 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12623, d113031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18559 q ha hb
    | true =>
      simp only [d12623, d113031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12624 q = 1) (hb : d113032 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12624, d113032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12624, d113032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12665 q = 1) (hb : d113038 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12665, d113038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12665, d113038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12666 q = 1) (hb : d113039 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12666, d113039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12666, d113039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12667 q = 1) (hb : d113040 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12667, d113040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12667, d113040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12668 q = 1) (hb : d113041 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12668, d113041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12668, d113041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18561 (p : Pattern) (ha : d12674 p = 1) (hb : d113060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12669 q = 1) (hb : d113055 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12669, d113055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18560 q ha hb
    | true =>
      simp only [d12669, d113055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12670 q = 1) (hb : d113056 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12670, d113056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12670, d113056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12671 q = 1) (hb : d113057 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12671, d113057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12671, d113057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12672 q = 1) (hb : d113058 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12672, d113058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12672, d113058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12673 q = 1) (hb : d113059 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12673, d113059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12673, d113059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12674 q = 1) (hb : d113060 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12674, d113060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12674, d113060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18562 (p : Pattern) (ha : d112872 p = 1) (hb : d114187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12313 q = 1) (hb : d112777 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d112777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18535 q ha hb
    | true =>
      simp only [d12313, d112777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7917 q ha hb
  have h2 (q : Pattern) (ha : d12314 q = 1) (hb : d112778 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d112778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d112778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12315 q = 1) (hb : d112779 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d112779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d112779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d68915 q = 1) (hb : d88338 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d68915, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7917 q hb ha
    | true =>
      simp only [d68915, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d68916 q = 1) (hb : d88339 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d68916, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68916, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68917 q = 1) (hb : d88340 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d68917, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68917, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112780 q = 1) (hb : d114185 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112780, d114185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d112780, d114185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d68918 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112871 q = 1) (hb : d114186 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d112871, d114186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112871, d114186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d112872 q = 1) (hb : d114187 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d112872, d114187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112872, d114187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18563 (p : Pattern) (ha : d112882 p = 1) (hb : d114275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18562 q ha hb
    | true =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d112877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18554 q ha hb
    | true =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d112878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112879 q = 1) (hb : d114272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112879, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112879, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112880 q = 1) (hb : d114273 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112880, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112880, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112881 q = 1) (hb : d114274 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112881, d114274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112881, d114274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112882 q = 1) (hb : d114275 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112882, d114275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112882, d114275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18564 (p : Pattern) (ha : d112892 p = 1) (hb : d114281 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112887 q = 1) (hb : d114276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112887, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18563 q ha hb
    | true =>
      simp only [d112887, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18555 q hb ha
  have h2 (q : Pattern) (ha : d112888 q = 1) (hb : d114277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112888, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112888, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112889 q = 1) (hb : d114278 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112889, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112889, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112890 q = 1) (hb : d114279 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112890, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112890, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112891 q = 1) (hb : d114280 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112891, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112891, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112892 q = 1) (hb : d114281 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112892, d114281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112892, d114281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18565 (p : Pattern) (ha : d112895 p = 1) (hb : d114284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18562 q ha hb
    | true =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d112877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18554 q ha hb
    | true =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d112878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112879 q = 1) (hb : d114272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112879, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112879, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112880 q = 1) (hb : d114273 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112880, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112880, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112881 q = 1) (hb : d114274 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112881, d114274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112881, d114274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112895 q = 1) (hb : d114284 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112895, d114284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112895, d114284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18566 (p : Pattern) (ha : d112902 p = 1) (hb : d114290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112887 q = 1) (hb : d114276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112887, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18563 q ha hb
    | true =>
      simp only [d112887, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18555 q hb ha
  have h2 (q : Pattern) (ha : d112888 q = 1) (hb : d114277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112888, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112888, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112889 q = 1) (hb : d114278 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112889, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112889, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112890 q = 1) (hb : d114279 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112890, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112890, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112891 q = 1) (hb : d114280 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112891, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112891, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112897 q = 1) (hb : d114285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112897, d114285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18565 q ha hb
    | true =>
      simp only [d112897, d114285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18556 q hb ha
  have h7 (q : Pattern) (ha : d112898 q = 1) (hb : d114286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112898, d114286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112898, d114286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112899 q = 1) (hb : d114287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112899, d114287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112899, d114287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d112900 q = 1) (hb : d114288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112900, d114288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112900, d114288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112901 q = 1) (hb : d114289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112901, d114289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112901, d114289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112902 q = 1) (hb : d114290 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112902, d114290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112902, d114290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18567 (p : Pattern) (ha : d12475 p = 1) (hb : d112909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d112877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18554 q ha hb
    | true =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d112878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d112883 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d112883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d112883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d112884 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d112884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d112884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12474 q = 1) (hb : d112908 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12474, d112908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12474, d112908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12475 q = 1) (hb : d112909 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12475, d112909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12475, d112909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18568 (p : Pattern) (ha : d12485 p = 1) (hb : d112919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d112877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18554 q ha hb
    | true =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d112878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d112883 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d112883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d112883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12483 q = 1) (hb : d112917 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12483, d112917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12483, d112917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12484 q = 1) (hb : d112918 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12484, d112918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12484, d112918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12485 q = 1) (hb : d112919 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12485, d112919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12485, d112919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18569 (p : Pattern) (ha : d112907 p = 1) (hb : d114295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18562 q ha hb
    | true =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d112877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18554 q ha hb
    | true =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d112878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112879 q = 1) (hb : d114272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112879, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112879, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112880 q = 1) (hb : d114273 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112880, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112880, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112906 q = 1) (hb : d114294 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112906, d114294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112906, d114294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112907 q = 1) (hb : d114295 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112907, d114295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112907, d114295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18570 (p : Pattern) (ha : d112916 p = 1) (hb : d114302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18562 q ha hb
    | true =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d112877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18554 q ha hb
    | true =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d112878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112879 q = 1) (hb : d114272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112879, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112879, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112914 q = 1) (hb : d114300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112914, d114300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112914, d114300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112915 q = 1) (hb : d114301 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112915, d114301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112915, d114301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112916 q = 1) (hb : d114302 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112916, d114302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112916, d114302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18571 (p : Pattern) (ha : d12489 p = 1) (hb : d112923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d52292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d321 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d547 q = 1) (hb : d52294 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d547, d52294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d547, d52294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12489 q = 1) (hb : d112923 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12489, d112923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12489, d112923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro18572 (p : Pattern) (ha : d112936 p = 1) (hb : d114311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12490 q = 1) (hb : d112924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12490, d112924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18571 q ha hb
    | true =>
      simp only [d12490, d112924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18535 q ha hb
  have h2 (q : Pattern) (ha : d12491 q = 1) (hb : d112925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12491, d112925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12491, d112925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12492 q = 1) (hb : d112926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12492, d112926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12492, d112926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112930 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d112931 q = 1) (hb : d114306 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d112931, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18535 q hb ha
    | true =>
      simp only [d112931, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112932 q = 1) (hb : d114307 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d112932, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112932, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112933 q = 1) (hb : d114308 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d112933, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112933, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112934 q = 1) (hb : d114309 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112934, d114309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d112934, d114309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112780 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112935 q = 1) (hb : d114310 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d112935, d114310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112935, d114310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d112936 q = 1) (hb : d114311 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d112936, d114311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112936, d114311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18573 (p : Pattern) (ha : d112942 p = 1) (hb : d114317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112937 q = 1) (hb : d114312 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112937, d114312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18572 q ha hb
    | true =>
      simp only [d112937, d114312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112938 q = 1) (hb : d114313 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112938, d114313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112938, d114313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112873 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18562 q ha hb
    | true =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112874 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112939 q = 1) (hb : d114314 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112939, d114314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112939, d114314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112940 q = 1) (hb : d114315 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112940, d114315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112940, d114315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112941 q = 1) (hb : d114316 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112941, d114316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112941, d114316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112942 q = 1) (hb : d114317 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112942, d114317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112942, d114317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18574 (p : Pattern) (ha : d112948 p = 1) (hb : d114323 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18562 q ha hb
    | true =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112945 q = 1) (hb : d114320 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112945, d114320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112945, d114320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112946 q = 1) (hb : d114321 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112946, d114321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112946, d114321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112947 q = 1) (hb : d114322 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112947, d114322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112947, d114322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112948 q = 1) (hb : d114323 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112948, d114323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112948, d114323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18575 (p : Pattern) (ha : d112954 p = 1) (hb : d114329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112910 q = 1) (hb : d114296 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112910, d114296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18569 q ha hb
    | true =>
      simp only [d112910, d114296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18567 q hb ha
  have h2 (q : Pattern) (ha : d112911 q = 1) (hb : d114297 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112911, d114297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112911, d114297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112912 q = 1) (hb : d114298 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112912, d114298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112912, d114298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112913 q = 1) (hb : d114299 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112913, d114299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112913, d114299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112920 q = 1) (hb : d114303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112920, d114303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18570 q ha hb
    | true =>
      simp only [d112920, d114303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18568 q hb ha
  have h6 (q : Pattern) (ha : d112921 q = 1) (hb : d114304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112921, d114304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112921, d114304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112922 q = 1) (hb : d114305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112922, d114305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112922, d114305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112943 q = 1) (hb : d114318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112943, d114318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18573 q ha hb
    | true =>
      simp only [d112943, d114318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18563 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112887 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112944 q = 1) (hb : d114319 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112944, d114319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112944, d114319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d112949 q = 1) (hb : d114324 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112949, d114324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18574 q ha hb
    | true =>
      simp only [d112949, d114324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112950 q = 1) (hb : d114325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112950, d114325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112950, d114325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112951 q = 1) (hb : d114326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112951, d114326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112951, d114326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d112952 q = 1) (hb : d114327 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112952, d114327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112952, d114327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112953 q = 1) (hb : d114328 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112953, d114328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112953, d114328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112954 q = 1) (hb : d114329 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112954, d114329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112954, d114329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro18576 (p : Pattern) (ha : d12545 p = 1) (hb : d112956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d112877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18554 q ha hb
    | true =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d112878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d112883 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d112883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d112883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d112884 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d112884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d112884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12474 q = 1) (hb : d112908 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12474, d112908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12474, d112908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12545 q = 1) (hb : d112956 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12545, d112956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12545, d112956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18577 (p : Pattern) (ha : d12551 p = 1) (hb : d112962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d112877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18554 q ha hb
    | true =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d112878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d112883 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d112883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d112883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12483 q = 1) (hb : d112917 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12483, d112917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12483, d112917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12484 q = 1) (hb : d112918 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12484, d112918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12484, d112918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12551 q = 1) (hb : d112962 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12551, d112962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12551, d112962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18578 (p : Pattern) (ha : d112955 p = 1) (hb : d114330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18562 q ha hb
    | true =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d112877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18554 q ha hb
    | true =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d112878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112879 q = 1) (hb : d114272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112879, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112879, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112880 q = 1) (hb : d114273 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112880, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112880, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112906 q = 1) (hb : d114294 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112906, d114294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112906, d114294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112955 q = 1) (hb : d114330 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112955, d114330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112955, d114330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18579 (p : Pattern) (ha : d112961 p = 1) (hb : d114335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18562 q ha hb
    | true =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d112877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18554 q ha hb
    | true =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d112878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112879 q = 1) (hb : d114272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112879, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112879, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112914 q = 1) (hb : d114300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112914, d114300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112914, d114300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112915 q = 1) (hb : d114301 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112915, d114301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112915, d114301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112961 q = 1) (hb : d114335 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112961, d114335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112961, d114335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18580 (p : Pattern) (ha : d112966 p = 1) (hb : d114339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112937 q = 1) (hb : d114312 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112937, d114312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18572 q ha hb
    | true =>
      simp only [d112937, d114312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112938 q = 1) (hb : d114313 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112938, d114313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112938, d114313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112873 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18562 q ha hb
    | true =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112874 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112939 q = 1) (hb : d114314 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112939, d114314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112939, d114314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112940 q = 1) (hb : d114315 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112940, d114315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112940, d114315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112941 q = 1) (hb : d114316 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112941, d114316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112941, d114316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112966 q = 1) (hb : d114339 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112966, d114339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112966, d114339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18581 (p : Pattern) (ha : d112969 p = 1) (hb : d114342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18562 q ha hb
    | true =>
      simp only [d112873, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112945 q = 1) (hb : d114320 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112945, d114320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112945, d114320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112946 q = 1) (hb : d114321 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112946, d114321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112946, d114321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112947 q = 1) (hb : d114322 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112947, d114322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112947, d114322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112969 q = 1) (hb : d114342 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112969, d114342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112969, d114342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro18582 (p : Pattern) (ha : d112975 p = 1) (hb : d114348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112910 q = 1) (hb : d114296 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112910, d114296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18569 q ha hb
    | true =>
      simp only [d112910, d114296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18567 q hb ha
  have h2 (q : Pattern) (ha : d112911 q = 1) (hb : d114297 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112911, d114297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112911, d114297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112912 q = 1) (hb : d114298 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112912, d114298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112912, d114298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112913 q = 1) (hb : d114299 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112913, d114299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112913, d114299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112920 q = 1) (hb : d114303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112920, d114303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18570 q ha hb
    | true =>
      simp only [d112920, d114303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18568 q hb ha
  have h6 (q : Pattern) (ha : d112921 q = 1) (hb : d114304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112921, d114304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112921, d114304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112922 q = 1) (hb : d114305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112922, d114305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112922, d114305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112943 q = 1) (hb : d114318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112943, d114318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18573 q ha hb
    | true =>
      simp only [d112943, d114318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18563 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112887 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112944 q = 1) (hb : d114319 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112944, d114319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112944, d114319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d112949 q = 1) (hb : d114324 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112949, d114324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18574 q ha hb
    | true =>
      simp only [d112949, d114324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112950 q = 1) (hb : d114325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112950, d114325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112950, d114325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112951 q = 1) (hb : d114326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112951, d114326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112951, d114326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d112952 q = 1) (hb : d114327 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112952, d114327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112952, d114327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112953 q = 1) (hb : d114328 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112953, d114328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112953, d114328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112957 q = 1) (hb : d114331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112957, d114331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18578 q ha hb
    | true =>
      simp only [d112957, d114331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18576 q hb ha
  have h17 (q : Pattern) (ha : d112958 q = 1) (hb : d114332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112958, d114332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112958, d114332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d112959 q = 1) (hb : d114333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112959, d114333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d112959, d114333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d112960 q = 1) (hb : d114334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112960, d114334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112960, d114334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d112963 q = 1) (hb : d114336 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112963, d114336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18579 q ha hb
    | true =>
      simp only [d112963, d114336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18577 q hb ha
  have h21 (q : Pattern) (ha : d112964 q = 1) (hb : d114337 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112964, d114337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112964, d114337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d112965 q = 1) (hb : d114338 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112965, d114338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d112965, d114338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d112967 q = 1) (hb : d114340 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112967, d114340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18580 q ha hb
    | true =>
      simp only [d112967, d114340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18565 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d112897 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d112968 q = 1) (hb : d114341 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112968, d114341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d112968, d114341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d112970 q = 1) (hb : d114343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112970, d114343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18581 q ha hb
    | true =>
      simp only [d112970, d114343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d112971 q = 1) (hb : d114344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112971, d114344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d112971, d114344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d112972 q = 1) (hb : d114345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112972, d114345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d112972, d114345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d112973 q = 1) (hb : d114346 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112973, d114346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d112973, d114346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d112974 q = 1) (hb : d114347 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112974, d114347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d112974, d114347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d112975 q = 1) (hb : d114348 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112975, d114348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d112975, d114348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro18583 (p : Pattern) (ha : d112982 p = 1) (hb : d114350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112887 q = 1) (hb : d114276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112887, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18563 q ha hb
    | true =>
      simp only [d112887, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18555 q hb ha
  have h2 (q : Pattern) (ha : d112888 q = 1) (hb : d114277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112888, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112888, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112889 q = 1) (hb : d114278 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112889, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112889, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112890 q = 1) (hb : d114279 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112890, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112890, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112891 q = 1) (hb : d114280 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112891, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112891, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12569 q = 1) (hb : d112977 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12569, d112977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18555 q ha hb
    | true =>
      simp only [d12569, d112977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12570 q = 1) (hb : d112978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12570, d112978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12570, d112978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12571 q = 1) (hb : d112979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12571, d112979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12571, d112979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12572 q = 1) (hb : d112980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12572, d112980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12572, d112980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12573 q = 1) (hb : d112981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12573, d112981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12573, d112981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112982 q = 1) (hb : d114350 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112982, d114350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112982, d114350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro18584 (p : Pattern) (ha : d112995 p = 1) (hb : d114357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112967 q = 1) (hb : d114340 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112967, d114340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18580 q ha hb
    | true =>
      simp only [d112967, d114340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18565 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112897 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112968 q = 1) (hb : d114341 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112968, d114341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112968, d114341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d112970 q = 1) (hb : d114343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112970, d114343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18581 q ha hb
    | true =>
      simp only [d112970, d114343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112971 q = 1) (hb : d114344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112971, d114344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112971, d114344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112972 q = 1) (hb : d114345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112972, d114345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112972, d114345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112993 q = 1) (hb : d114355 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112993, d114355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112993, d114355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112994 q = 1) (hb : d114356 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112994, d114356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112994, d114356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112995 q = 1) (hb : d114357 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112995, d114357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112995, d114357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro18585 (p : Pattern) (ha : d12595 p = 1) (hb : d113003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d661 q = 1) (hb : d52365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d662 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d412 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
  have h8 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d413 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d414 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d415 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d663 q = 1) (hb : d52367 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d663, d52367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d663, d52367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12595 q = 1) (hb : d113003 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12595, d113003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12595, d113003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro18586 (p : Pattern) (ha : d113018 p = 1) (hb : d114368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12596 q = 1) (hb : d113004 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12596, d113004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18585 q ha hb
    | true =>
      simp only [d12596, d113004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18547 q ha hb
  have h2 (q : Pattern) (ha : d12597 q = 1) (hb : d113005 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12597, d113005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12597, d113005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12598 q = 1) (hb : d113006 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12598, d113006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12598, d113006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113012 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113013 q = 1) (hb : d114363 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113013, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18547 q hb ha
    | true =>
      simp only [d113013, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113014 q = 1) (hb : d114364 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113014, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113014, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113015 q = 1) (hb : d114365 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113015, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113015, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113016 q = 1) (hb : d114366 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113016, d114366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113016, d114366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112838 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113017 q = 1) (hb : d114367 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113017, d114367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113017, d114367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113018 q = 1) (hb : d114368 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113018, d114368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113018, d114368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18587 (p : Pattern) (ha : d113022 p = 1) (hb : d114241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12387 q = 1) (hb : d112835 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d112835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18547 q ha hb
    | true =>
      simp only [d12387, d112835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q ha hb
  have h2 (q : Pattern) (ha : d12388 q = 1) (hb : d112836 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d112836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d112836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12389 q = 1) (hb : d112837 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d112837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d112837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75841 q = 1) (hb : d88402 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d75841, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q hb ha
    | true =>
      simp only [d75841, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75842 q = 1) (hb : d88403 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d75842, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75842, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75843 q = 1) (hb : d88404 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d75843, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75843, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112838 q = 1) (hb : d114239 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112838, d114239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d112838, d114239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d75844 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113021 q = 1) (hb : d114240 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113021, d114240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113021, d114240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113022 q = 1) (hb : d114241 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113022, d114241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113022, d114241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18588 (p : Pattern) (ha : d113028 p = 1) (hb : d114374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113019 q = 1) (hb : d114369 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113019, d114369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18586 q ha hb
    | true =>
      simp only [d113019, d114369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113020 q = 1) (hb : d114370 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113020, d114370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113020, d114370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113023 q = 1) (hb : d114242 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113023, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18587 q ha hb
    | true =>
      simp only [d113023, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113024 q = 1) (hb : d114243 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113024, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113024, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113025 q = 1) (hb : d114371 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113025, d114371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113025, d114371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113026 q = 1) (hb : d114372 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113026, d114372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113026, d114372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113027 q = 1) (hb : d114373 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113027, d114373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113027, d114373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113028 q = 1) (hb : d114374 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113028, d114374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113028, d114374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18589 (p : Pattern) (ha : d113036 p = 1) (hb : d114378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113023 q = 1) (hb : d114242 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113023, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18587 q ha hb
    | true =>
      simp only [d113023, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113024 q = 1) (hb : d114243 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113024, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113024, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12623 q = 1) (hb : d113031 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12623, d113031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18559 q ha hb
    | true =>
      simp only [d12623, d113031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12624 q = 1) (hb : d113032 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12624, d113032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12624, d113032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113033 q = 1) (hb : d114375 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113033, d114375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113033, d114375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113034 q = 1) (hb : d114376 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113034, d114376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113034, d114376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113035 q = 1) (hb : d114377 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113035, d114377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113035, d114377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113036 q = 1) (hb : d114378 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113036, d114378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113036, d114378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18590 (p : Pattern) (ha : d113047 p = 1) (hb : d114384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113023 q = 1) (hb : d114242 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113023, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18587 q ha hb
    | true =>
      simp only [d113023, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113024 q = 1) (hb : d114243 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113024, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113024, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113044 q = 1) (hb : d114381 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113044, d114381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113044, d114381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113045 q = 1) (hb : d114382 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113045, d114382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113045, d114382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113046 q = 1) (hb : d114383 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113046, d114383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113046, d114383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113047 q = 1) (hb : d114384 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113047, d114384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113047, d114384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro18591 (p : Pattern) (ha : d113053 p = 1) (hb : d114390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113037 q = 1) (hb : d114379 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113037, d114379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18588 q ha hb
    | true =>
      simp only [d113037, d114379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18589 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113042 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113043 q = 1) (hb : d114380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113043, d114380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113043, d114380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113048 q = 1) (hb : d114385 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113048, d114385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18590 q ha hb
    | true =>
      simp only [d113048, d114385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113049 q = 1) (hb : d114386 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113049, d114386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113049, d114386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113050 q = 1) (hb : d114387 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113050, d114387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113050, d114387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113051 q = 1) (hb : d114388 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113051, d114388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113051, d114388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113052 q = 1) (hb : d114389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113052, d114389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113052, d114389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113053 q = 1) (hb : d114390 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113053, d114390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113053, d114390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro18592 (p : Pattern) (ha : d113066 p = 1) (hb : d114396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112893 q = 1) (hb : d114282 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112893, d114282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112893, d114282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18564 q ha hb
  have h2 (q : Pattern) (ha : d112894 q = 1) (hb : d114283 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112894, d114283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112894, d114283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112903 q = 1) (hb : d114291 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112903, d114291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18564 q ha hb
    | true =>
      simp only [d112903, d114291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18566 q ha hb
  have h4 (q : Pattern) (ha : d112904 q = 1) (hb : d114292 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112904, d114292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112904, d114292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112905 q = 1) (hb : d114293 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112905, d114293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112905, d114293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112976 q = 1) (hb : d114349 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112976, d114349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18575 q ha hb
    | true =>
      simp only [d112976, d114349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18582 q ha hb
  have h7 (q : Pattern) (ha : d112989 q = 1) (hb : d114351 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112989, d114351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18583 q ha hb
    | true =>
      simp only [d112989, d114351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18557 q hb ha
  have h8 (q : Pattern) (ha : d112990 q = 1) (hb : d114352 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112990, d114352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112990, d114352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112991 q = 1) (hb : d114353 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112991, d114353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112991, d114353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d112992 q = 1) (hb : d114354 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112992, d114354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112992, d114354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112996 q = 1) (hb : d114358 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112996, d114358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112996, d114358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18584 q ha hb
  have h12 (q : Pattern) (ha : d12590 q = 1) (hb : d112998 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12590, d112998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12590, d112998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18558 q ha hb
  have h13 (q : Pattern) (ha : d112999 q = 1) (hb : d114359 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112999, d114359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112999, d114359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d113000 q = 1) (hb : d114360 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113000, d114360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113000, d114360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d113001 q = 1) (hb : d114361 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113001, d114361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d113001, d114361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d113002 q = 1) (hb : d114362 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113002, d114362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113002, d114362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113054 q = 1) (hb : d114391 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113054, d114391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113054, d114391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18591 q ha hb
  have h18 (q : Pattern) (ha : d12675 q = 1) (hb : d113061 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12675, d113061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12675, d113061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18561 q ha hb
  have h19 (q : Pattern) (ha : d113062 q = 1) (hb : d114392 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113062, d114392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113062, d114392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d113063 q = 1) (hb : d114393 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113063, d114393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113063, d114393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d113064 q = 1) (hb : d114394 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113064, d114394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d113064, d114394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d113065 q = 1) (hb : d114395 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113065, d114395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113065, d114395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113066 q = 1) (hb : d114396 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113066, d114396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113066, d114396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro18593 (p : Pattern) (ha : d113072 p = 1) (hb : d114402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113067 q = 1) (hb : d114397 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113067, d114397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113067, d114397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18592 q ha hb
  have h2 (q : Pattern) (ha : d113068 q = 1) (hb : d114398 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113068, d114398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113068, d114398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113069 q = 1) (hb : d114399 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113069, d114399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113069, d114399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113070 q = 1) (hb : d114400 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113070, d114400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113070, d114400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113071 q = 1) (hb : d114401 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113071, d114401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113071, d114401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113072 q = 1) (hb : d114402 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113072, d114402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113072, d114402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18594 (p : Pattern) (ha : d12697 p = 1) (hb : d113083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4914 q = 1) (hb : d69007 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d69007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7931 q ha hb
    | true =>
      simp only [d4914, d69007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q ha hb
  have h2 (q : Pattern) (ha : d4915 q = 1) (hb : d69008 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d69008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d69008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4916 q = 1) (hb : d69009 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d69009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d69009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4917 q = 1) (hb : d69010 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d69010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4917, d69010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12696 q = 1) (hb : d113082 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12696, d113082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12696, d113082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12697 q = 1) (hb : d113083 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12697, d113083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12697, d113083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18595 (p : Pattern) (ha : d12707 p = 1) (hb : d113093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d113084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18594 q ha hb
    | true =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d113085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d113090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d113090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d113090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d113091 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d113091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d113091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12706 q = 1) (hb : d113092 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12706, d113092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12706, d113092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12707 q = 1) (hb : d113093 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12707, d113093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12707, d113093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18596 (p : Pattern) (ha : d12717 p = 1) (hb : d113103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d113084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18594 q ha hb
    | true =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d113085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d113090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d113090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d113090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d113091 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d113091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d113091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12706 q = 1) (hb : d113092 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12706, d113092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12706, d113092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12717 q = 1) (hb : d113103 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12717, d113103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12717, d113103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18597 (p : Pattern) (ha : d12839 p = 1) (hb : d113195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12828 q = 1) (hb : d113184 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12828, d113184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18595 q ha hb
    | true =>
      simp only [d12828, d113184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12829 q = 1) (hb : d113185 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12829, d113185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12829, d113185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12830 q = 1) (hb : d113186 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12830, d113186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12830, d113186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12831 q = 1) (hb : d113187 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12831, d113187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12831, d113187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12832 q = 1) (hb : d113188 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12832, d113188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12832, d113188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12834 q = 1) (hb : d113190 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12834, d113190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18596 q ha hb
    | true =>
      simp only [d12834, d113190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12835 q = 1) (hb : d113191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12835, d113191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12835, d113191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12836 q = 1) (hb : d113192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12836, d113192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12836, d113192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12837 q = 1) (hb : d113193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12837, d113193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12837, d113193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12838 q = 1) (hb : d113194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12838, d113194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12838, d113194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12839 q = 1) (hb : d113195 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12839, d113195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12839, d113195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18598 (p : Pattern) (ha : d12848 p = 1) (hb : d113204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12834 q = 1) (hb : d113190 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12834, d113190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18596 q ha hb
    | true =>
      simp only [d12834, d113190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12835 q = 1) (hb : d113191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12835, d113191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12835, d113191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12836 q = 1) (hb : d113192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12836, d113192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12836, d113192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12837 q = 1) (hb : d113193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12837, d113193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12837, d113193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12838 q = 1) (hb : d113194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12838, d113194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12838, d113194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12848 q = 1) (hb : d113204 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12848, d113204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12848, d113204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18599 (p : Pattern) (ha : d12885 p = 1) (hb : d113241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6211 q = 1) (hb : d75962 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d75962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10873 q ha hb
    | true =>
      simp only [d6211, d75962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q ha hb
  have h2 (q : Pattern) (ha : d6212 q = 1) (hb : d75963 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d75963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d75963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6213 q = 1) (hb : d75964 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d75964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d75964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6214 q = 1) (hb : d75965 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d75965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6214, d75965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12884 q = 1) (hb : d113240 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12884, d113240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12884, d113240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12885 q = 1) (hb : d113241 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12885, d113241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12885, d113241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18600 (p : Pattern) (ha : d12935 p = 1) (hb : d113252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12886 q = 1) (hb : d113242 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12886, d113242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18599 q ha hb
    | true =>
      simp only [d12886, d113242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12887 q = 1) (hb : d113243 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12887, d113243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12887, d113243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12932 q = 1) (hb : d113249 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12932, d113249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12932, d113249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12933 q = 1) (hb : d113250 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12933, d113250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12933, d113250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12934 q = 1) (hb : d113251 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12934, d113251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12934, d113251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12935 q = 1) (hb : d113252 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12935, d113252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12935, d113252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18601 (p : Pattern) (ha : d12941 p = 1) (hb : d113271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12936 q = 1) (hb : d113266 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12936, d113266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18600 q ha hb
    | true =>
      simp only [d12936, d113266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12937 q = 1) (hb : d113267 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12937, d113267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12937, d113267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12938 q = 1) (hb : d113268 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12938, d113268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12938, d113268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12939 q = 1) (hb : d113269 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12939, d113269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12939, d113269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12940 q = 1) (hb : d113270 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12940, d113270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12940, d113270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12941 q = 1) (hb : d113271 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12941, d113271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12941, d113271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18602 (p : Pattern) (ha : d113079 p = 1) (hb : d114406 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12688 q = 1) (hb : d113074 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12688, d113074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18571 q ha hb
    | true =>
      simp only [d12688, d113074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7931 q ha hb
  have h2 (q : Pattern) (ha : d12689 q = 1) (hb : d113075 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12689, d113075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12689, d113075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12690 q = 1) (hb : d113076 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12690, d113076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12690, d113076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52439 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69007 q = 1) (hb : d88489 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69007, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7931 q hb ha
    | true =>
      simp only [d69007, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69008 q = 1) (hb : d88490 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69008, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69008, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69009 q = 1) (hb : d88491 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69009, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69009, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113077 q = 1) (hb : d114404 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113077, d114404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113077, d114404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d69010 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113078 q = 1) (hb : d114405 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113078, d114405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113078, d114405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113079 q = 1) (hb : d114406 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113079, d114406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113079, d114406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18603 (p : Pattern) (ha : d113089 p = 1) (hb : d114412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18602 q ha hb
    | true =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d113084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18594 q ha hb
    | true =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d113085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113086 q = 1) (hb : d114409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113086, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113086, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113087 q = 1) (hb : d114410 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113087, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113087, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113088 q = 1) (hb : d114411 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113088, d114411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113088, d114411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113089 q = 1) (hb : d114412 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113089, d114412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113089, d114412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18604 (p : Pattern) (ha : d113099 p = 1) (hb : d114418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113094 q = 1) (hb : d114413 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113094, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18603 q ha hb
    | true =>
      simp only [d113094, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18595 q hb ha
  have h2 (q : Pattern) (ha : d113095 q = 1) (hb : d114414 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113095, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113095, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113096 q = 1) (hb : d114415 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113096, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113096, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113097 q = 1) (hb : d114416 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113097, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113097, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113098 q = 1) (hb : d114417 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113098, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113098, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113099 q = 1) (hb : d114418 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113099, d114418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113099, d114418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18605 (p : Pattern) (ha : d113102 p = 1) (hb : d114421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18602 q ha hb
    | true =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d113084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18594 q ha hb
    | true =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d113085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113086 q = 1) (hb : d114409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113086, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113086, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113087 q = 1) (hb : d114410 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113087, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113087, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113088 q = 1) (hb : d114411 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113088, d114411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113088, d114411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113102 q = 1) (hb : d114421 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113102, d114421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113102, d114421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18606 (p : Pattern) (ha : d113109 p = 1) (hb : d114427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113094 q = 1) (hb : d114413 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113094, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18603 q ha hb
    | true =>
      simp only [d113094, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18595 q hb ha
  have h2 (q : Pattern) (ha : d113095 q = 1) (hb : d114414 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113095, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113095, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113096 q = 1) (hb : d114415 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113096, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113096, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113097 q = 1) (hb : d114416 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113097, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113097, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113098 q = 1) (hb : d114417 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113098, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113098, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113104 q = 1) (hb : d114422 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113104, d114422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18605 q ha hb
    | true =>
      simp only [d113104, d114422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18596 q hb ha
  have h7 (q : Pattern) (ha : d113105 q = 1) (hb : d114423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113105, d114423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113105, d114423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113106 q = 1) (hb : d114424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113106, d114424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113106, d114424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113107 q = 1) (hb : d114425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113107, d114425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113107, d114425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113108 q = 1) (hb : d114426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113108, d114426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113108, d114426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113109 q = 1) (hb : d114427 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113109, d114427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113109, d114427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18607 (p : Pattern) (ha : d12730 p = 1) (hb : d113116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d113084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18594 q ha hb
    | true =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d113085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d113090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d113090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d113090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d113091 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d113091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d113091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12729 q = 1) (hb : d113115 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12729, d113115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12729, d113115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12730 q = 1) (hb : d113116 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12730, d113116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12730, d113116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18608 (p : Pattern) (ha : d12740 p = 1) (hb : d113126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d113084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18594 q ha hb
    | true =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d113085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d113090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d113090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d113090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12738 q = 1) (hb : d113124 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12738, d113124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12738, d113124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12739 q = 1) (hb : d113125 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12739, d113125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12739, d113125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12740 q = 1) (hb : d113126 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12740, d113126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12740, d113126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18609 (p : Pattern) (ha : d113114 p = 1) (hb : d114432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18602 q ha hb
    | true =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d113084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18594 q ha hb
    | true =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d113085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113086 q = 1) (hb : d114409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113086, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113086, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113087 q = 1) (hb : d114410 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113087, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113087, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113113 q = 1) (hb : d114431 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113113, d114431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113113, d114431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113114 q = 1) (hb : d114432 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113114, d114432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113114, d114432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18610 (p : Pattern) (ha : d113123 p = 1) (hb : d114439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18602 q ha hb
    | true =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d113084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18594 q ha hb
    | true =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d113085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113086 q = 1) (hb : d114409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113086, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113086, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113121 q = 1) (hb : d114437 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113121, d114437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113121, d114437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113122 q = 1) (hb : d114438 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113122, d114438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113122, d114438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113123 q = 1) (hb : d114439 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113123, d114439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113123, d114439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18611 (p : Pattern) (ha : d12744 p = 1) (hb : d113130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d834 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
    | true =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d835 q = 1) (hb : d52512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d836 q = 1) (hb : d52513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d836, d52513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d836, d52513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d837 q = 1) (hb : d52514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d837, d52514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d837, d52514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d545 q = 1) (hb : d52292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d546 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d838 q = 1) (hb : d52515 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d838, d52515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d838, d52515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12744 q = 1) (hb : d113130 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12744, d113130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12744, d113130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro18612 (p : Pattern) (ha : d113143 p = 1) (hb : d114448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12745 q = 1) (hb : d113131 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12745, d113131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18611 q ha hb
    | true =>
      simp only [d12745, d113131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18571 q ha hb
  have h2 (q : Pattern) (ha : d12746 q = 1) (hb : d113132 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12746, d113132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12746, d113132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12747 q = 1) (hb : d113133 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12747, d113133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12747, d113133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113137 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113138 q = 1) (hb : d114443 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113138, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18571 q hb ha
    | true =>
      simp only [d113138, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113139 q = 1) (hb : d114444 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113139, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113139, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113140 q = 1) (hb : d114445 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113140, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113140, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113141 q = 1) (hb : d114446 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113141, d114446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113141, d114446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113077 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113142 q = 1) (hb : d114447 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113142, d114447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113142, d114447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113143 q = 1) (hb : d114448 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113143, d114448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113143, d114448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18613 (p : Pattern) (ha : d113149 p = 1) (hb : d114454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113144 q = 1) (hb : d114449 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113144, d114449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18612 q ha hb
    | true =>
      simp only [d113144, d114449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113145 q = 1) (hb : d114450 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113145, d114450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113145, d114450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113080 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18602 q ha hb
    | true =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113081 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113146 q = 1) (hb : d114451 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113146, d114451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113146, d114451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113147 q = 1) (hb : d114452 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113147, d114452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113147, d114452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113148 q = 1) (hb : d114453 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113148, d114453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113148, d114453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113149 q = 1) (hb : d114454 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113149, d114454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113149, d114454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18614 (p : Pattern) (ha : d113155 p = 1) (hb : d114460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18602 q ha hb
    | true =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113152 q = 1) (hb : d114457 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113152, d114457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113152, d114457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113153 q = 1) (hb : d114458 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113153, d114458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113153, d114458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113154 q = 1) (hb : d114459 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113154, d114459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113154, d114459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113155 q = 1) (hb : d114460 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113155, d114460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113155, d114460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18615 (p : Pattern) (ha : d113161 p = 1) (hb : d114466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113117 q = 1) (hb : d114433 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113117, d114433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18609 q ha hb
    | true =>
      simp only [d113117, d114433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18607 q hb ha
  have h2 (q : Pattern) (ha : d113118 q = 1) (hb : d114434 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113118, d114434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113118, d114434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113119 q = 1) (hb : d114435 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113119, d114435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113119, d114435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113120 q = 1) (hb : d114436 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113120, d114436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113120, d114436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113127 q = 1) (hb : d114440 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113127, d114440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18610 q ha hb
    | true =>
      simp only [d113127, d114440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18608 q hb ha
  have h6 (q : Pattern) (ha : d113128 q = 1) (hb : d114441 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113128, d114441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113128, d114441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113129 q = 1) (hb : d114442 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113129, d114442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113129, d114442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113150 q = 1) (hb : d114455 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113150, d114455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18613 q ha hb
    | true =>
      simp only [d113150, d114455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18603 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113094 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113151 q = 1) (hb : d114456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113151, d114456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113151, d114456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113156 q = 1) (hb : d114461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113156, d114461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18614 q ha hb
    | true =>
      simp only [d113156, d114461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113157 q = 1) (hb : d114462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113157, d114462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113157, d114462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113158 q = 1) (hb : d114463 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113158, d114463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113158, d114463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113159 q = 1) (hb : d114464 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113159, d114464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113159, d114464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113160 q = 1) (hb : d114465 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113160, d114465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113160, d114465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113161 q = 1) (hb : d114466 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113161, d114466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113161, d114466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro18616 (p : Pattern) (ha : d12804 p = 1) (hb : d113163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d113084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18594 q ha hb
    | true =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d113085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d113090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d113090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d113090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d113091 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d113091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d113091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12729 q = 1) (hb : d113115 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12729, d113115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12729, d113115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12804 q = 1) (hb : d113163 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12804, d113163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12804, d113163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18617 (p : Pattern) (ha : d12810 p = 1) (hb : d113169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d113084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18594 q ha hb
    | true =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d113085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d113090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d113090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d113090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12738 q = 1) (hb : d113124 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12738, d113124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12738, d113124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12739 q = 1) (hb : d113125 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12739, d113125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12739, d113125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12810 q = 1) (hb : d113169 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12810, d113169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12810, d113169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18618 (p : Pattern) (ha : d113162 p = 1) (hb : d114467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18602 q ha hb
    | true =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d113084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18594 q ha hb
    | true =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d113085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113086 q = 1) (hb : d114409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113086, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113086, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113087 q = 1) (hb : d114410 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113087, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113087, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113113 q = 1) (hb : d114431 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113113, d114431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113113, d114431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113162 q = 1) (hb : d114467 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113162, d114467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113162, d114467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18619 (p : Pattern) (ha : d113168 p = 1) (hb : d114472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18602 q ha hb
    | true =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d113084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18594 q ha hb
    | true =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d113085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113086 q = 1) (hb : d114409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113086, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113086, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113121 q = 1) (hb : d114437 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113121, d114437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113121, d114437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113122 q = 1) (hb : d114438 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113122, d114438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113122, d114438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113168 q = 1) (hb : d114472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113168, d114472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113168, d114472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18620 (p : Pattern) (ha : d113173 p = 1) (hb : d114476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113144 q = 1) (hb : d114449 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113144, d114449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18612 q ha hb
    | true =>
      simp only [d113144, d114449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113145 q = 1) (hb : d114450 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113145, d114450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113145, d114450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113080 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18602 q ha hb
    | true =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113081 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113146 q = 1) (hb : d114451 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113146, d114451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113146, d114451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113147 q = 1) (hb : d114452 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113147, d114452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113147, d114452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113148 q = 1) (hb : d114453 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113148, d114453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113148, d114453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113173 q = 1) (hb : d114476 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113173, d114476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113173, d114476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18621 (p : Pattern) (ha : d113176 p = 1) (hb : d114479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18602 q ha hb
    | true =>
      simp only [d113080, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113152 q = 1) (hb : d114457 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113152, d114457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113152, d114457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113153 q = 1) (hb : d114458 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113153, d114458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113153, d114458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113154 q = 1) (hb : d114459 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113154, d114459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113154, d114459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113176 q = 1) (hb : d114479 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113176, d114479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113176, d114479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro18622 (p : Pattern) (ha : d113182 p = 1) (hb : d114485 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113117 q = 1) (hb : d114433 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113117, d114433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18609 q ha hb
    | true =>
      simp only [d113117, d114433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18607 q hb ha
  have h2 (q : Pattern) (ha : d113118 q = 1) (hb : d114434 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113118, d114434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113118, d114434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113119 q = 1) (hb : d114435 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113119, d114435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113119, d114435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113120 q = 1) (hb : d114436 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113120, d114436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113120, d114436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113127 q = 1) (hb : d114440 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113127, d114440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18610 q ha hb
    | true =>
      simp only [d113127, d114440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18608 q hb ha
  have h6 (q : Pattern) (ha : d113128 q = 1) (hb : d114441 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113128, d114441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113128, d114441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113129 q = 1) (hb : d114442 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113129, d114442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113129, d114442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113150 q = 1) (hb : d114455 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113150, d114455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18613 q ha hb
    | true =>
      simp only [d113150, d114455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18603 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113094 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113151 q = 1) (hb : d114456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113151, d114456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113151, d114456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113156 q = 1) (hb : d114461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113156, d114461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18614 q ha hb
    | true =>
      simp only [d113156, d114461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113157 q = 1) (hb : d114462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113157, d114462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113157, d114462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113158 q = 1) (hb : d114463 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113158, d114463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113158, d114463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113159 q = 1) (hb : d114464 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113159, d114464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113159, d114464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113160 q = 1) (hb : d114465 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113160, d114465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113160, d114465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113164 q = 1) (hb : d114468 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113164, d114468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18618 q ha hb
    | true =>
      simp only [d113164, d114468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18616 q hb ha
  have h17 (q : Pattern) (ha : d113165 q = 1) (hb : d114469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113165, d114469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113165, d114469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113166 q = 1) (hb : d114470 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113166, d114470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113166, d114470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d113167 q = 1) (hb : d114471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113167, d114471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113167, d114471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113170 q = 1) (hb : d114473 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113170, d114473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18619 q ha hb
    | true =>
      simp only [d113170, d114473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18617 q hb ha
  have h21 (q : Pattern) (ha : d113171 q = 1) (hb : d114474 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113171, d114474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113171, d114474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d113172 q = 1) (hb : d114475 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113172, d114475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113172, d114475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113174 q = 1) (hb : d114477 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113174, d114477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18620 q ha hb
    | true =>
      simp only [d113174, d114477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18605 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d113104 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d113175 q = 1) (hb : d114478 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113175, d114478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d113175, d114478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d113177 q = 1) (hb : d114480 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113177, d114480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18621 q ha hb
    | true =>
      simp only [d113177, d114480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d113178 q = 1) (hb : d114481 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113178, d114481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d113178, d114481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d113179 q = 1) (hb : d114482 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113179, d114482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d113179, d114482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d113180 q = 1) (hb : d114483 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113180, d114483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d113180, d114483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d113181 q = 1) (hb : d114484 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113181, d114484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113181, d114484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d113182 q = 1) (hb : d114485 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113182, d114485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113182, d114485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro18623 (p : Pattern) (ha : d113189 p = 1) (hb : d114487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113094 q = 1) (hb : d114413 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113094, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18603 q ha hb
    | true =>
      simp only [d113094, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18595 q hb ha
  have h2 (q : Pattern) (ha : d113095 q = 1) (hb : d114414 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113095, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113095, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113096 q = 1) (hb : d114415 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113096, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113096, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113097 q = 1) (hb : d114416 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113097, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113097, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113098 q = 1) (hb : d114417 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113098, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113098, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12828 q = 1) (hb : d113184 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12828, d113184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18595 q ha hb
    | true =>
      simp only [d12828, d113184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12829 q = 1) (hb : d113185 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12829, d113185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12829, d113185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12830 q = 1) (hb : d113186 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12830, d113186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12830, d113186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12831 q = 1) (hb : d113187 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12831, d113187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12831, d113187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12832 q = 1) (hb : d113188 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12832, d113188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12832, d113188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113189 q = 1) (hb : d114487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113189, d114487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113189, d114487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro18624 (p : Pattern) (ha : d113202 p = 1) (hb : d114494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113174 q = 1) (hb : d114477 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113174, d114477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18620 q ha hb
    | true =>
      simp only [d113174, d114477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18605 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113175 q = 1) (hb : d114478 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113175, d114478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113175, d114478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113177 q = 1) (hb : d114480 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113177, d114480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18621 q ha hb
    | true =>
      simp only [d113177, d114480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113178 q = 1) (hb : d114481 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113178, d114481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113178, d114481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113179 q = 1) (hb : d114482 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113179, d114482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113179, d114482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113200 q = 1) (hb : d114492 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113200, d114492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113200, d114492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113201 q = 1) (hb : d114493 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113201, d114493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113201, d114493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113202 q = 1) (hb : d114494 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113202, d114494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113202, d114494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro18625 (p : Pattern) (ha : d12854 p = 1) (hb : d113210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d965 q = 1) (hb : d52584 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d965, d52584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d965, d52584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
  have h2 (q : Pattern) (ha : d834 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
    | true =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d966 q = 1) (hb : d52585 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d966, d52585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d966, d52585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d835 q = 1) (hb : d52512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d967 q = 1) (hb : d52586 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d967, d52586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d967, d52586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d968 q = 1) (hb : d52587 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d968, d52587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d968, d52587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d659 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
  have h8 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d660 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d661 q = 1) (hb : d52365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d662 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d969 q = 1) (hb : d52588 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d969, d52588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d969, d52588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12854 q = 1) (hb : d113210 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12854, d113210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12854, d113210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro18626 (p : Pattern) (ha : d113229 p = 1) (hb : d114505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12855 q = 1) (hb : d113211 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12855, d113211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18625 q ha hb
    | true =>
      simp only [d12855, d113211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18585 q ha hb
  have h2 (q : Pattern) (ha : d12856 q = 1) (hb : d113212 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12856, d113212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12856, d113212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12857 q = 1) (hb : d113213 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12857, d113213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12857, d113213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113219 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113220 q = 1) (hb : d114500 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113220, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18585 q hb ha
    | true =>
      simp only [d113220, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113221 q = 1) (hb : d114501 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113221, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113221, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113222 q = 1) (hb : d114502 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113222, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113222, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113223 q = 1) (hb : d114503 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113223, d114503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113223, d114503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113227 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113228 q = 1) (hb : d114504 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113228, d114504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113228, d114504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113229 q = 1) (hb : d114505 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113229, d114505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113229, d114505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18627 (p : Pattern) (ha : d113233 p = 1) (hb : d114510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12868 q = 1) (hb : d113224 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12868, d113224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18585 q ha hb
    | true =>
      simp only [d12868, d113224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10873 q ha hb
  have h2 (q : Pattern) (ha : d12869 q = 1) (hb : d113225 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12869, d113225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12869, d113225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12870 q = 1) (hb : d113226 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12870, d113226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12870, d113226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52605 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75962 q = 1) (hb : d88553 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d75962, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10873 q hb ha
    | true =>
      simp only [d75962, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75963 q = 1) (hb : d88554 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d75963, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75963, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75964 q = 1) (hb : d88555 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d75964, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75964, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113227 q = 1) (hb : d114508 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113227, d114508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113227, d114508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d75965 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113232 q = 1) (hb : d114509 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113232, d114509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113232, d114509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113233 q = 1) (hb : d114510 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113233, d114510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113233, d114510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18628 (p : Pattern) (ha : d113239 p = 1) (hb : d114516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113230 q = 1) (hb : d114506 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113230, d114506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18626 q ha hb
    | true =>
      simp only [d113230, d114506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113231 q = 1) (hb : d114507 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113231, d114507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113231, d114507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113234 q = 1) (hb : d114511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113234, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18627 q ha hb
    | true =>
      simp only [d113234, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113235 q = 1) (hb : d114512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113235, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113235, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113236 q = 1) (hb : d114513 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113236, d114513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113236, d114513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113237 q = 1) (hb : d114514 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113237, d114514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113237, d114514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113238 q = 1) (hb : d114515 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113238, d114515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113238, d114515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113239 q = 1) (hb : d114516 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113239, d114516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113239, d114516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18629 (p : Pattern) (ha : d113247 p = 1) (hb : d114520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113234 q = 1) (hb : d114511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113234, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18627 q ha hb
    | true =>
      simp only [d113234, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113235 q = 1) (hb : d114512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113235, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113235, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12886 q = 1) (hb : d113242 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12886, d113242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18599 q ha hb
    | true =>
      simp only [d12886, d113242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12887 q = 1) (hb : d113243 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12887, d113243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12887, d113243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113244 q = 1) (hb : d114517 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113244, d114517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113244, d114517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113245 q = 1) (hb : d114518 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113245, d114518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113245, d114518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113246 q = 1) (hb : d114519 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113246, d114519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113246, d114519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113247 q = 1) (hb : d114520 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113247, d114520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113247, d114520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18630 (p : Pattern) (ha : d113258 p = 1) (hb : d114526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113234 q = 1) (hb : d114511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113234, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18627 q ha hb
    | true =>
      simp only [d113234, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113235 q = 1) (hb : d114512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113235, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113235, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113255 q = 1) (hb : d114523 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113255, d114523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113255, d114523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113256 q = 1) (hb : d114524 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113256, d114524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113256, d114524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113257 q = 1) (hb : d114525 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113257, d114525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113257, d114525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113258 q = 1) (hb : d114526 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113258, d114526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113258, d114526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro18631 (p : Pattern) (ha : d113264 p = 1) (hb : d114532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113248 q = 1) (hb : d114521 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113248, d114521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18628 q ha hb
    | true =>
      simp only [d113248, d114521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18629 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113253 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113254 q = 1) (hb : d114522 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113254, d114522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113254, d114522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113259 q = 1) (hb : d114527 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113259, d114527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18630 q ha hb
    | true =>
      simp only [d113259, d114527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113260 q = 1) (hb : d114528 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113260, d114528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113260, d114528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113261 q = 1) (hb : d114529 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113261, d114529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113261, d114529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113262 q = 1) (hb : d114530 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113262, d114530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113262, d114530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113263 q = 1) (hb : d114531 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113263, d114531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113263, d114531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113264 q = 1) (hb : d114532 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113264, d114532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113264, d114532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro18632 (p : Pattern) (ha : d113277 p = 1) (hb : d114538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113100 q = 1) (hb : d114419 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113100, d114419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113100, d114419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18604 q ha hb
  have h2 (q : Pattern) (ha : d113101 q = 1) (hb : d114420 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113101, d114420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113101, d114420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d113110 q = 1) (hb : d114428 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113110, d114428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18604 q ha hb
    | true =>
      simp only [d113110, d114428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18606 q ha hb
  have h4 (q : Pattern) (ha : d113111 q = 1) (hb : d114429 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113111, d114429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113111, d114429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113112 q = 1) (hb : d114430 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113112, d114430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113112, d114430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113183 q = 1) (hb : d114486 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113183, d114486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18615 q ha hb
    | true =>
      simp only [d113183, d114486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18622 q ha hb
  have h7 (q : Pattern) (ha : d113196 q = 1) (hb : d114488 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113196, d114488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18623 q ha hb
    | true =>
      simp only [d113196, d114488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18597 q hb ha
  have h8 (q : Pattern) (ha : d113197 q = 1) (hb : d114489 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113197, d114489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113197, d114489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113198 q = 1) (hb : d114490 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113198, d114490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113198, d114490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d113199 q = 1) (hb : d114491 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113199, d114491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113199, d114491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113203 q = 1) (hb : d114495 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113203, d114495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113203, d114495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18624 q ha hb
  have h12 (q : Pattern) (ha : d12849 q = 1) (hb : d113205 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12849, d113205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12849, d113205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18598 q ha hb
  have h13 (q : Pattern) (ha : d113206 q = 1) (hb : d114496 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113206, d114496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113206, d114496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d113207 q = 1) (hb : d114497 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113207, d114497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113207, d114497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d113208 q = 1) (hb : d114498 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113208, d114498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d113208, d114498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d113209 q = 1) (hb : d114499 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113209, d114499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113209, d114499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113265 q = 1) (hb : d114533 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113265, d114533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113265, d114533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18631 q ha hb
  have h18 (q : Pattern) (ha : d12942 q = 1) (hb : d113272 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12942, d113272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12942, d113272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18601 q ha hb
  have h19 (q : Pattern) (ha : d113273 q = 1) (hb : d114534 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113273, d114534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113273, d114534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d113274 q = 1) (hb : d114535 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113274, d114535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113274, d114535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d113275 q = 1) (hb : d114536 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113275, d114536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d113275, d114536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d113276 q = 1) (hb : d114537 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113276, d114537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113276, d114537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113277 q = 1) (hb : d114538 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113277, d114538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113277, d114538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro18633 (p : Pattern) (ha : d113283 p = 1) (hb : d114544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113278 q = 1) (hb : d114539 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113278, d114539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113278, d114539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18632 q ha hb
  have h2 (q : Pattern) (ha : d113279 q = 1) (hb : d114540 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113279, d114540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113279, d114540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113280 q = 1) (hb : d114541 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113280, d114541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113280, d114541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113281 q = 1) (hb : d114542 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113281, d114542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113281, d114542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113282 q = 1) (hb : d114543 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113282, d114543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113282, d114543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113283 q = 1) (hb : d114544 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113283, d114544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113283, d114544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18634 (p : Pattern) (ha : d12961 p = 1) (hb : d113291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1123 q = 1) (hb : d52704 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1124 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1127 q = 1) (hb : d52708 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d52708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1127, d52708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12961 q = 1) (hb : d113291 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12961, d113291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12961, d113291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18635 (p : Pattern) (ha : d12971 p = 1) (hb : d113301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12962 q = 1) (hb : d113292 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12962, d113292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7945 q ha hb
    | true =>
      simp only [d12962, d113292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18634 q ha hb
  have h2 (q : Pattern) (ha : d12963 q = 1) (hb : d113293 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12963, d113293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12963, d113293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12964 q = 1) (hb : d113294 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12964, d113294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12964, d113294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12965 q = 1) (hb : d113295 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12965, d113295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12965, d113295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12970 q = 1) (hb : d113300 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12970, d113300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12970, d113300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12971 q = 1) (hb : d113301 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12971, d113301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12971, d113301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18636 (p : Pattern) (ha : d12981 p = 1) (hb : d113311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d113302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18635 q ha hb
    | true =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d113303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d113308 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d113308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d113308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d113309 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d113309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d113309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12980 q = 1) (hb : d113310 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12980, d113310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12980, d113310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12981 q = 1) (hb : d113311 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12981, d113311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12981, d113311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18637 (p : Pattern) (ha : d12991 p = 1) (hb : d113321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d113302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18635 q ha hb
    | true =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d113303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d113308 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d113308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d113308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d113309 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d113309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d113309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12980 q = 1) (hb : d113310 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12980, d113310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12980, d113310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12991 q = 1) (hb : d113321 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12991, d113321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12991, d113321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18638 (p : Pattern) (ha : d13140 p = 1) (hb : d113432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13129 q = 1) (hb : d113421 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13129, d113421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18636 q ha hb
    | true =>
      simp only [d13129, d113421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13130 q = 1) (hb : d113422 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13130, d113422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13130, d113422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13131 q = 1) (hb : d113423 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13131, d113423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13131, d113423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13132 q = 1) (hb : d113424 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13132, d113424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13132, d113424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13133 q = 1) (hb : d113425 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13133, d113425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13133, d113425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13135 q = 1) (hb : d113427 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13135, d113427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18637 q ha hb
    | true =>
      simp only [d13135, d113427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13136 q = 1) (hb : d113428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13136, d113428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13136, d113428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13137 q = 1) (hb : d113429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13137, d113429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13137, d113429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13138 q = 1) (hb : d113430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13138, d113430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13138, d113430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13139 q = 1) (hb : d113431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13139, d113431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13139, d113431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13140 q = 1) (hb : d113432 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13140, d113432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13140, d113432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18639 (p : Pattern) (ha : d13149 p = 1) (hb : d113441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13135 q = 1) (hb : d113427 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13135, d113427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18637 q ha hb
    | true =>
      simp only [d13135, d113427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13136 q = 1) (hb : d113428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13136, d113428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13136, d113428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13137 q = 1) (hb : d113429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13137, d113429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13137, d113429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13138 q = 1) (hb : d113430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13138, d113430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13138, d113430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13139 q = 1) (hb : d113431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13139, d113431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13139, d113431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13149 q = 1) (hb : d113441 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13149, d113441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13149, d113441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18640 (p : Pattern) (ha : d13190 p = 1) (hb : d113482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1391 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1392 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1393 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1394 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1394, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1400 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d52888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1400, d52888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13190 q = 1) (hb : d113482 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13190, d113482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13190, d113482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18641 (p : Pattern) (ha : d13196 p = 1) (hb : d113488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13191 q = 1) (hb : d113483 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13191, d113483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10886 q ha hb
    | true =>
      simp only [d13191, d113483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18640 q ha hb
  have h2 (q : Pattern) (ha : d13192 q = 1) (hb : d113484 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13192, d113484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13192, d113484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13193 q = 1) (hb : d113485 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13193, d113485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13193, d113485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13194 q = 1) (hb : d113486 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13194, d113486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13194, d113486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13195 q = 1) (hb : d113487 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13195, d113487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13195, d113487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13196 q = 1) (hb : d113488 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13196, d113488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13196, d113488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18642 (p : Pattern) (ha : d13260 p = 1) (hb : d113507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13197 q = 1) (hb : d113489 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d113489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18641 q ha hb
    | true =>
      simp only [d13197, d113489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13198 q = 1) (hb : d113490 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d113490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d113490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13257 q = 1) (hb : d113504 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13257, d113504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13257, d113504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13258 q = 1) (hb : d113505 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13258, d113505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13258, d113505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13259 q = 1) (hb : d113506 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13259, d113506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13259, d113506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13260 q = 1) (hb : d113507 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13260, d113507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13260, d113507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18643 (p : Pattern) (ha : d13266 p = 1) (hb : d113526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13261 q = 1) (hb : d113521 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13261, d113521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18642 q ha hb
    | true =>
      simp only [d13261, d113521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13262 q = 1) (hb : d113522 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13262, d113522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13262, d113522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13263 q = 1) (hb : d113523 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13263, d113523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13263, d113523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13264 q = 1) (hb : d113524 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13264, d113524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13264, d113524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13265 q = 1) (hb : d113525 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13265, d113525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13265, d113525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13266 q = 1) (hb : d113526 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13266, d113526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13266, d113526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18644 (p : Pattern) (ha : d12956 p = 1) (hb : d113286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1100 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1101 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1102 q = 1) (hb : d52683 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1103 q = 1) (hb : d52684 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1103, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1112 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1113 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1114 q = 1) (hb : d52695 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1114, d52695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1114, d52695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12956 q = 1) (hb : d113286 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12956, d113286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12956, d113286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro18645 (p : Pattern) (ha : d113297 p = 1) (hb : d114549 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12957 q = 1) (hb : d113287 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d113287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18644 q ha hb
    | true =>
      simp only [d12957, d113287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7945 q ha hb
  have h2 (q : Pattern) (ha : d12958 q = 1) (hb : d113288 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d113288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d113288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12959 q = 1) (hb : d113289 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d113289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d113289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d69113 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69114 q = 1) (hb : d88641 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69114, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7945 q hb ha
    | true =>
      simp only [d69114, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69115 q = 1) (hb : d88642 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69115, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69115, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69116 q = 1) (hb : d88643 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69116, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69116, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113290 q = 1) (hb : d114547 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113290, d114547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113290, d114547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113295 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113296 q = 1) (hb : d114548 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113296, d114548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113296, d114548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113297 q = 1) (hb : d114549 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113297, d114549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113297, d114549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18646 (p : Pattern) (ha : d113307 p = 1) (hb : d114555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18645 q ha hb
    | true =>
      simp only [d113298, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d113302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18635 q ha hb
    | true =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d113303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113304 q = 1) (hb : d114552 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113304, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113304, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113305 q = 1) (hb : d114553 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113305, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113305, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113306 q = 1) (hb : d114554 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113306, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113306, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113307 q = 1) (hb : d114555 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113307, d114555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113307, d114555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18647 (p : Pattern) (ha : d113317 p = 1) (hb : d114561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113312 q = 1) (hb : d114556 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113312, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18646 q ha hb
    | true =>
      simp only [d113312, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18636 q hb ha
  have h2 (q : Pattern) (ha : d113313 q = 1) (hb : d114557 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113313, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113313, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113314 q = 1) (hb : d114558 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113314, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113314, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113315 q = 1) (hb : d114559 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113315, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113315, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113316 q = 1) (hb : d114560 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113316, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113316, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113317 q = 1) (hb : d114561 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113317, d114561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113317, d114561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18648 (p : Pattern) (ha : d113320 p = 1) (hb : d114564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18645 q ha hb
    | true =>
      simp only [d113298, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d113302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18635 q ha hb
    | true =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d113303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113304 q = 1) (hb : d114552 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113304, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113304, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113305 q = 1) (hb : d114553 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113305, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113305, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113306 q = 1) (hb : d114554 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113306, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113306, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113320 q = 1) (hb : d114564 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113320, d114564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113320, d114564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18649 (p : Pattern) (ha : d113327 p = 1) (hb : d114570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113312 q = 1) (hb : d114556 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113312, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18646 q ha hb
    | true =>
      simp only [d113312, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18636 q hb ha
  have h2 (q : Pattern) (ha : d113313 q = 1) (hb : d114557 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113313, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113313, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113314 q = 1) (hb : d114558 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113314, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113314, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113315 q = 1) (hb : d114559 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113315, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113315, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113316 q = 1) (hb : d114560 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113316, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113316, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113322 q = 1) (hb : d114565 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113322, d114565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18648 q ha hb
    | true =>
      simp only [d113322, d114565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18637 q hb ha
  have h7 (q : Pattern) (ha : d113323 q = 1) (hb : d114566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113323, d114566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113323, d114566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113324 q = 1) (hb : d114567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113324, d114567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113324, d114567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113325 q = 1) (hb : d114568 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113325, d114568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113325, d114568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113326 q = 1) (hb : d114569 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113326, d114569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113326, d114569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113327 q = 1) (hb : d114570 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113327, d114570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113327, d114570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18650 (p : Pattern) (ha : d13004 p = 1) (hb : d113334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d113302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18635 q ha hb
    | true =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d113303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d113308 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d113308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d113308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d113309 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d113309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d113309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13003 q = 1) (hb : d113333 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13003, d113333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13003, d113333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13004 q = 1) (hb : d113334 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13004, d113334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13004, d113334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18651 (p : Pattern) (ha : d13014 p = 1) (hb : d113344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d113302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18635 q ha hb
    | true =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d113303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d113308 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d113308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d113308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13012 q = 1) (hb : d113342 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13012, d113342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13012, d113342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13013 q = 1) (hb : d113343 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13013, d113343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13013, d113343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13014 q = 1) (hb : d113344 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13014, d113344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13014, d113344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18652 (p : Pattern) (ha : d113332 p = 1) (hb : d114575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18645 q ha hb
    | true =>
      simp only [d113298, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d113302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18635 q ha hb
    | true =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d113303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113304 q = 1) (hb : d114552 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113304, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113304, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113305 q = 1) (hb : d114553 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113305, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113305, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113331 q = 1) (hb : d114574 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113331, d114574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113331, d114574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113332 q = 1) (hb : d114575 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113332, d114575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113332, d114575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18653 (p : Pattern) (ha : d113341 p = 1) (hb : d114582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18645 q ha hb
    | true =>
      simp only [d113298, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d113302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18635 q ha hb
    | true =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d113303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113304 q = 1) (hb : d114552 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113304, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113304, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113339 q = 1) (hb : d114580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113339, d114580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113339, d114580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113340 q = 1) (hb : d114581 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113340, d114581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113340, d114581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113341 q = 1) (hb : d114582 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113341, d114582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113341, d114582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18654 (p : Pattern) (ha : d13018 p = 1) (hb : d113348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1210 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
    | true =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1211 q = 1) (hb : d52792 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1212 q = 1) (hb : d52793 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1212, d52793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1212, d52793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1213 q = 1) (hb : d52794 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1213, d52794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1213, d52794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1100 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1101 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1102 q = 1) (hb : d52683 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1103 q = 1) (hb : d52684 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1103, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1214 q = 1) (hb : d52795 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1214, d52795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1214, d52795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13018 q = 1) (hb : d113348 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13018, d113348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13018, d113348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro18655 (p : Pattern) (ha : d113366 p = 1) (hb : d114591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13019 q = 1) (hb : d113349 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13019, d113349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18654 q ha hb
    | true =>
      simp only [d13019, d113349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18644 q ha hb
  have h2 (q : Pattern) (ha : d13020 q = 1) (hb : d113350 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13020, d113350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13020, d113350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13021 q = 1) (hb : d113351 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13021, d113351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13021, d113351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113360 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113361 q = 1) (hb : d114586 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113361, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18644 q hb ha
    | true =>
      simp only [d113361, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113362 q = 1) (hb : d114587 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113362, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113362, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113363 q = 1) (hb : d114588 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113363, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113363, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113364 q = 1) (hb : d114589 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113364, d114589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113364, d114589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113290 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113365 q = 1) (hb : d114590 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113365, d114590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113365, d114590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113366 q = 1) (hb : d114591 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113366, d114591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113366, d114591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18656 (p : Pattern) (ha : d113370 p = 1) (hb : d114549 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12957 q = 1) (hb : d113287 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d113287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18644 q ha hb
    | true =>
      simp only [d12957, d113287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7945 q ha hb
  have h2 (q : Pattern) (ha : d12958 q = 1) (hb : d113288 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d113288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d113288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12959 q = 1) (hb : d113289 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d113289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d113289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d69113 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69114 q = 1) (hb : d88641 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69114, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7945 q hb ha
    | true =>
      simp only [d69114, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69115 q = 1) (hb : d88642 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69115, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69115, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69116 q = 1) (hb : d88643 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69116, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69116, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113290 q = 1) (hb : d114547 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113290, d114547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113290, d114547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d69117 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113369 q = 1) (hb : d114548 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113369, d114548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113369, d114548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113370 q = 1) (hb : d114549 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113370, d114549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113370, d114549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18657 (p : Pattern) (ha : d113376 p = 1) (hb : d114597 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113367 q = 1) (hb : d114592 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113367, d114592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18655 q ha hb
    | true =>
      simp only [d113367, d114592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113368 q = 1) (hb : d114593 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113368, d114593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113368, d114593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113371 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113371, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18656 q ha hb
    | true =>
      simp only [d113371, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113372 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113372, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113372, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113373 q = 1) (hb : d114594 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113373, d114594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113373, d114594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113374 q = 1) (hb : d114595 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113374, d114595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113374, d114595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113375 q = 1) (hb : d114596 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113375, d114596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113375, d114596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113376 q = 1) (hb : d114597 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113376, d114597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113376, d114597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18658 (p : Pattern) (ha : d113380 p = 1) (hb : d114555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113371 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113371, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18656 q ha hb
    | true =>
      simp only [d113371, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113372 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113372, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113372, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d113302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18635 q ha hb
    | true =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d113303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113377 q = 1) (hb : d114552 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113377, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113377, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113378 q = 1) (hb : d114553 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113378, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113378, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113379 q = 1) (hb : d114554 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113379, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113379, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113380 q = 1) (hb : d114555 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113380, d114555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113380, d114555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18659 (p : Pattern) (ha : d113386 p = 1) (hb : d114603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18645 q ha hb
    | true =>
      simp only [d113298, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113383 q = 1) (hb : d114600 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113383, d114600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113383, d114600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113384 q = 1) (hb : d114601 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113384, d114601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113384, d114601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113385 q = 1) (hb : d114602 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113385, d114602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113385, d114602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113386 q = 1) (hb : d114603 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113386, d114603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113386, d114603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18660 (p : Pattern) (ha : d113392 p = 1) (hb : d114609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113335 q = 1) (hb : d114576 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113335, d114576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18652 q ha hb
    | true =>
      simp only [d113335, d114576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18650 q hb ha
  have h2 (q : Pattern) (ha : d113336 q = 1) (hb : d114577 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113336, d114577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113336, d114577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113337 q = 1) (hb : d114578 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113337, d114578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113337, d114578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113338 q = 1) (hb : d114579 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113338, d114579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113338, d114579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113345 q = 1) (hb : d114583 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113345, d114583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18653 q ha hb
    | true =>
      simp only [d113345, d114583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18651 q hb ha
  have h6 (q : Pattern) (ha : d113346 q = 1) (hb : d114584 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113346, d114584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113346, d114584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113347 q = 1) (hb : d114585 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113347, d114585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113347, d114585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113381 q = 1) (hb : d114598 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113381, d114598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18657 q ha hb
    | true =>
      simp only [d113381, d114598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18658 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113312 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113382 q = 1) (hb : d114599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113382, d114599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113382, d114599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113387 q = 1) (hb : d114604 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113387, d114604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18659 q ha hb
    | true =>
      simp only [d113387, d114604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113388 q = 1) (hb : d114605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113388, d114605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113388, d114605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113389 q = 1) (hb : d114606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113389, d114606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113389, d114606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113390 q = 1) (hb : d114607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113390, d114607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113390, d114607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113391 q = 1) (hb : d114608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113391, d114608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113391, d114608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113392 q = 1) (hb : d114609 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113392, d114609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113392, d114609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro18661 (p : Pattern) (ha : d13099 p = 1) (hb : d113394 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d113302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18635 q ha hb
    | true =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d113303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d113308 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d113308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d113308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d113309 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d113309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d113309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13003 q = 1) (hb : d113333 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13003, d113333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13003, d113333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13099 q = 1) (hb : d113394 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13099, d113394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13099, d113394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18662 (p : Pattern) (ha : d13105 p = 1) (hb : d113400 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d113302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18635 q ha hb
    | true =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d113303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d113308 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d113308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d113308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13012 q = 1) (hb : d113342 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13012, d113342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13012, d113342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13013 q = 1) (hb : d113343 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13013, d113343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13013, d113343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13105 q = 1) (hb : d113400 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13105, d113400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13105, d113400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18663 (p : Pattern) (ha : d113393 p = 1) (hb : d114610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18645 q ha hb
    | true =>
      simp only [d113298, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d113302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18635 q ha hb
    | true =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d113303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113304 q = 1) (hb : d114552 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113304, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113304, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113305 q = 1) (hb : d114553 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113305, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113305, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113331 q = 1) (hb : d114574 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113331, d114574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113331, d114574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113393 q = 1) (hb : d114610 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113393, d114610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113393, d114610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18664 (p : Pattern) (ha : d113399 p = 1) (hb : d114615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18645 q ha hb
    | true =>
      simp only [d113298, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d113302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18635 q ha hb
    | true =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d113303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113304 q = 1) (hb : d114552 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113304, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113304, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113339 q = 1) (hb : d114580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113339, d114580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113339, d114580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113340 q = 1) (hb : d114581 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113340, d114581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113340, d114581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113399 q = 1) (hb : d114615 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113399, d114615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113399, d114615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18665 (p : Pattern) (ha : d113404 p = 1) (hb : d114619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113367 q = 1) (hb : d114592 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113367, d114592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18655 q ha hb
    | true =>
      simp only [d113367, d114592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113368 q = 1) (hb : d114593 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113368, d114593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113368, d114593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113371 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113371, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18656 q ha hb
    | true =>
      simp only [d113371, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113372 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113372, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113372, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113373 q = 1) (hb : d114594 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113373, d114594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113373, d114594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113374 q = 1) (hb : d114595 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113374, d114595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113374, d114595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113375 q = 1) (hb : d114596 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113375, d114596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113375, d114596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113404 q = 1) (hb : d114619 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113404, d114619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113404, d114619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18666 (p : Pattern) (ha : d113405 p = 1) (hb : d114564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113371 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113371, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18656 q ha hb
    | true =>
      simp only [d113371, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113372 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113372, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113372, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d113302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18635 q ha hb
    | true =>
      simp only [d12972, d113302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d113303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d113303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113377 q = 1) (hb : d114552 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113377, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113377, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113378 q = 1) (hb : d114553 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113378, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113378, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113379 q = 1) (hb : d114554 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113379, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113379, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113405 q = 1) (hb : d114564 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113405, d114564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113405, d114564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18667 (p : Pattern) (ha : d113408 p = 1) (hb : d114622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18645 q ha hb
    | true =>
      simp only [d113298, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113383 q = 1) (hb : d114600 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113383, d114600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113383, d114600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113384 q = 1) (hb : d114601 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113384, d114601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113384, d114601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113385 q = 1) (hb : d114602 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113385, d114602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113385, d114602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113408 q = 1) (hb : d114622 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113408, d114622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113408, d114622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro18668 (p : Pattern) (ha : d113414 p = 1) (hb : d114628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113335 q = 1) (hb : d114576 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113335, d114576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18652 q ha hb
    | true =>
      simp only [d113335, d114576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18650 q hb ha
  have h2 (q : Pattern) (ha : d113336 q = 1) (hb : d114577 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113336, d114577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113336, d114577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113337 q = 1) (hb : d114578 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113337, d114578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113337, d114578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113338 q = 1) (hb : d114579 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113338, d114579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113338, d114579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113345 q = 1) (hb : d114583 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113345, d114583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18653 q ha hb
    | true =>
      simp only [d113345, d114583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18651 q hb ha
  have h6 (q : Pattern) (ha : d113346 q = 1) (hb : d114584 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113346, d114584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113346, d114584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113347 q = 1) (hb : d114585 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113347, d114585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113347, d114585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113381 q = 1) (hb : d114598 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113381, d114598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18657 q ha hb
    | true =>
      simp only [d113381, d114598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18658 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113312 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113382 q = 1) (hb : d114599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113382, d114599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113382, d114599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113387 q = 1) (hb : d114604 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113387, d114604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18659 q ha hb
    | true =>
      simp only [d113387, d114604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113388 q = 1) (hb : d114605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113388, d114605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113388, d114605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113389 q = 1) (hb : d114606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113389, d114606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113389, d114606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113390 q = 1) (hb : d114607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113390, d114607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113390, d114607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113391 q = 1) (hb : d114608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113391, d114608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113391, d114608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113395 q = 1) (hb : d114611 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113395, d114611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18663 q ha hb
    | true =>
      simp only [d113395, d114611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18661 q hb ha
  have h17 (q : Pattern) (ha : d113396 q = 1) (hb : d114612 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113396, d114612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113396, d114612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113397 q = 1) (hb : d114613 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113397, d114613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113397, d114613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d113398 q = 1) (hb : d114614 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113398, d114614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113398, d114614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113401 q = 1) (hb : d114616 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113401, d114616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18664 q ha hb
    | true =>
      simp only [d113401, d114616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18662 q hb ha
  have h21 (q : Pattern) (ha : d113402 q = 1) (hb : d114617 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113402, d114617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113402, d114617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d113403 q = 1) (hb : d114618 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113403, d114618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113403, d114618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113406 q = 1) (hb : d114620 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113406, d114620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18665 q ha hb
    | true =>
      simp only [d113406, d114620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18666 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d113322 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d113407 q = 1) (hb : d114621 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113407, d114621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d113407, d114621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d113409 q = 1) (hb : d114623 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113409, d114623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18667 q ha hb
    | true =>
      simp only [d113409, d114623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d113410 q = 1) (hb : d114624 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113410, d114624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d113410, d114624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d113411 q = 1) (hb : d114625 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113411, d114625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d113411, d114625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d113412 q = 1) (hb : d114626 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113412, d114626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d113412, d114626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d113413 q = 1) (hb : d114627 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113413, d114627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113413, d114627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d113414 q = 1) (hb : d114628 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113414, d114628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113414, d114628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro18669 (p : Pattern) (ha : d113426 p = 1) (hb : d114630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113416 q = 1) (hb : d114556 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113416, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18658 q ha hb
    | true =>
      simp only [d113416, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18636 q hb ha
  have h2 (q : Pattern) (ha : d113417 q = 1) (hb : d114557 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113417, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113417, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113418 q = 1) (hb : d114558 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113418, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113418, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113419 q = 1) (hb : d114559 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113419, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113419, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113420 q = 1) (hb : d114560 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113420, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113420, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13129 q = 1) (hb : d113421 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13129, d113421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18636 q ha hb
    | true =>
      simp only [d13129, d113421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13130 q = 1) (hb : d113422 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13130, d113422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13130, d113422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13131 q = 1) (hb : d113423 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13131, d113423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13131, d113423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13132 q = 1) (hb : d113424 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13132, d113424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13132, d113424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13133 q = 1) (hb : d113425 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13133, d113425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13133, d113425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113426 q = 1) (hb : d114630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113426, d114630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113426, d114630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro18670 (p : Pattern) (ha : d113439 p = 1) (hb : d114637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113406 q = 1) (hb : d114620 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113406, d114620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18665 q ha hb
    | true =>
      simp only [d113406, d114620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18666 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113322 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113407 q = 1) (hb : d114621 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113407, d114621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113407, d114621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113409 q = 1) (hb : d114623 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113409, d114623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18667 q ha hb
    | true =>
      simp only [d113409, d114623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113410 q = 1) (hb : d114624 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113410, d114624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113410, d114624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113411 q = 1) (hb : d114625 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113411, d114625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113411, d114625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113437 q = 1) (hb : d114635 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113437, d114635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113437, d114635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113438 q = 1) (hb : d114636 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113438, d114636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113438, d114636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113439 q = 1) (hb : d114637 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113439, d114637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113439, d114637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro18671 (p : Pattern) (ha : d13155 p = 1) (hb : d113447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1376 q = 1) (hb : d52864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1376, d52864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1376, d52864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
  have h2 (q : Pattern) (ha : d1210 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
    | true =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1377 q = 1) (hb : d52865 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1377, d52865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1377, d52865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1211 q = 1) (hb : d52792 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1378 q = 1) (hb : d52866 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1378, d52866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1378, d52866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1379 q = 1) (hb : d52867 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1379, d52867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1379, d52867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1380 q = 1) (hb : d52868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
  have h8 (q : Pattern) (ha : d1100 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1381 q = 1) (hb : d52869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1381, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1101 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1382 q = 1) (hb : d52870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1382, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1383 q = 1) (hb : d52871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1383, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1384 q = 1) (hb : d52872 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1384, d52872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1384, d52872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13155 q = 1) (hb : d113447 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13155, d113447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13155, d113447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro18672 (p : Pattern) (ha : d13156 p = 1) (hb : d113448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1380 q = 1) (hb : d52868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
  have h2 (q : Pattern) (ha : d1100 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1381 q = 1) (hb : d52869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1381, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1101 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1382 q = 1) (hb : d52870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1382, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1383 q = 1) (hb : d52871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1383, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1385 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
  have h8 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1386 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1387 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1388 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1388, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1389 q = 1) (hb : d52877 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1389, d52877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1389, d52877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13156 q = 1) (hb : d113448 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13156, d113448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13156, d113448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro18673 (p : Pattern) (ha : d113471 p = 1) (hb : d114648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13157 q = 1) (hb : d113449 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13157, d113449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18671 q ha hb
    | true =>
      simp only [d13157, d113449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18672 q ha hb
  have h2 (q : Pattern) (ha : d13158 q = 1) (hb : d113450 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13158, d113450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13158, d113450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13159 q = 1) (hb : d113451 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13159, d113451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13159, d113451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113461 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113462 q = 1) (hb : d114643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113462, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18672 q hb ha
    | true =>
      simp only [d113462, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113463 q = 1) (hb : d114644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113463, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113463, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113464 q = 1) (hb : d114645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113464, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113464, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113465 q = 1) (hb : d114646 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113465, d114646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113465, d114646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113469 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113470 q = 1) (hb : d114647 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113470, d114647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113470, d114647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113471 q = 1) (hb : d114648 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113471, d114648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113471, d114648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18674 (p : Pattern) (ha : d113475 p = 1) (hb : d114653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13174 q = 1) (hb : d113466 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d113466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18672 q ha hb
    | true =>
      simp only [d13174, d113466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10886 q ha hb
  have h2 (q : Pattern) (ha : d13175 q = 1) (hb : d113467 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d113467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d113467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13176 q = 1) (hb : d113468 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d113468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d113468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76095 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76096 q = 1) (hb : d88705 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76096, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10886 q hb ha
    | true =>
      simp only [d76096, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76097 q = 1) (hb : d88706 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76097, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76097, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76098 q = 1) (hb : d88707 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76098, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76098, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113469 q = 1) (hb : d114651 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113469, d114651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113469, d114651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d76099 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113474 q = 1) (hb : d114652 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113474, d114652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113474, d114652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113475 q = 1) (hb : d114653 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113475, d114653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113475, d114653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18675 (p : Pattern) (ha : d113481 p = 1) (hb : d114659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113472 q = 1) (hb : d114649 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113472, d114649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18673 q ha hb
    | true =>
      simp only [d113472, d114649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113473 q = 1) (hb : d114650 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113473, d114650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113473, d114650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113476 q = 1) (hb : d114654 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113476, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18674 q ha hb
    | true =>
      simp only [d113476, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113477 q = 1) (hb : d114655 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113477, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113477, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113478 q = 1) (hb : d114656 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113478, d114656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113478, d114656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113479 q = 1) (hb : d114657 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113479, d114657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113479, d114657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113480 q = 1) (hb : d114658 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113480, d114658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113480, d114658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113481 q = 1) (hb : d114659 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113481, d114659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113481, d114659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18676 (p : Pattern) (ha : d113494 p = 1) (hb : d114663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113476 q = 1) (hb : d114654 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113476, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18674 q ha hb
    | true =>
      simp only [d113476, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113477 q = 1) (hb : d114655 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113477, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113477, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13197 q = 1) (hb : d113489 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d113489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18641 q ha hb
    | true =>
      simp only [d13197, d113489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13198 q = 1) (hb : d113490 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d113490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d113490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113491 q = 1) (hb : d114660 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113491, d114660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113491, d114660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113492 q = 1) (hb : d114661 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113492, d114661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113492, d114661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113493 q = 1) (hb : d114662 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113493, d114662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113493, d114662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113494 q = 1) (hb : d114663 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113494, d114663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113494, d114663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18677 (p : Pattern) (ha : d113497 p = 1) (hb : d114653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13174 q = 1) (hb : d113466 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d113466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18672 q ha hb
    | true =>
      simp only [d13174, d113466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10886 q ha hb
  have h2 (q : Pattern) (ha : d13175 q = 1) (hb : d113467 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d113467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d113467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13176 q = 1) (hb : d113468 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d113468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d113468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76095 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76096 q = 1) (hb : d88705 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76096, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10886 q hb ha
    | true =>
      simp only [d76096, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76097 q = 1) (hb : d88706 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76097, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76097, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76098 q = 1) (hb : d88707 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76098, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76098, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113469 q = 1) (hb : d114651 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113469, d114651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113469, d114651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113486 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113496 q = 1) (hb : d114652 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113496, d114652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113496, d114652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113497 q = 1) (hb : d114653 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113497, d114653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113497, d114653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18678 (p : Pattern) (ha : d113513 p = 1) (hb : d114669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113498 q = 1) (hb : d114654 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113498, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18677 q ha hb
    | true =>
      simp only [d113498, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113499 q = 1) (hb : d114655 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113499, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113499, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113510 q = 1) (hb : d114666 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113510, d114666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113510, d114666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113511 q = 1) (hb : d114667 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113511, d114667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113511, d114667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113512 q = 1) (hb : d114668 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113512, d114668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113512, d114668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113513 q = 1) (hb : d114669 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113513, d114669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113513, d114669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro18679 (p : Pattern) (ha : d113519 p = 1) (hb : d114675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113495 q = 1) (hb : d114664 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113495, d114664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18675 q ha hb
    | true =>
      simp only [d113495, d114664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18676 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113508 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113509 q = 1) (hb : d114665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113509, d114665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113509, d114665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113514 q = 1) (hb : d114670 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113514, d114670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18678 q ha hb
    | true =>
      simp only [d113514, d114670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113515 q = 1) (hb : d114671 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113515, d114671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113515, d114671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113516 q = 1) (hb : d114672 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113516, d114672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113516, d114672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113517 q = 1) (hb : d114673 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113517, d114673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113517, d114673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113518 q = 1) (hb : d114674 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113518, d114674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113518, d114674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113519 q = 1) (hb : d114675 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113519, d114675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113519, d114675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro18680 (p : Pattern) (ha : d113532 p = 1) (hb : d114681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113318 q = 1) (hb : d114562 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113318, d114562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113318, d114562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18647 q ha hb
  have h2 (q : Pattern) (ha : d113319 q = 1) (hb : d114563 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113319, d114563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113319, d114563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d113328 q = 1) (hb : d114571 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113328, d114571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18647 q ha hb
    | true =>
      simp only [d113328, d114571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18649 q ha hb
  have h4 (q : Pattern) (ha : d113329 q = 1) (hb : d114572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113329, d114572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113329, d114572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113330 q = 1) (hb : d114573 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113330, d114573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113330, d114573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113415 q = 1) (hb : d114629 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113415, d114629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18660 q ha hb
    | true =>
      simp only [d113415, d114629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18668 q ha hb
  have h7 (q : Pattern) (ha : d113433 q = 1) (hb : d114631 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113433, d114631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18669 q ha hb
    | true =>
      simp only [d113433, d114631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18638 q hb ha
  have h8 (q : Pattern) (ha : d113434 q = 1) (hb : d114632 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113434, d114632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113434, d114632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113435 q = 1) (hb : d114633 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113435, d114633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113435, d114633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d113436 q = 1) (hb : d114634 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113436, d114634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113436, d114634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113440 q = 1) (hb : d114638 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113440, d114638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113440, d114638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18670 q ha hb
  have h12 (q : Pattern) (ha : d13150 q = 1) (hb : d113442 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13150, d113442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13150, d113442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18639 q ha hb
  have h13 (q : Pattern) (ha : d113443 q = 1) (hb : d114639 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113443, d114639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113443, d114639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d113444 q = 1) (hb : d114640 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113444, d114640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113444, d114640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d113445 q = 1) (hb : d114641 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113445, d114641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d113445, d114641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d113446 q = 1) (hb : d114642 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113446, d114642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113446, d114642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113520 q = 1) (hb : d114676 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113520, d114676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113520, d114676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18679 q ha hb
  have h18 (q : Pattern) (ha : d13267 q = 1) (hb : d113527 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13267, d113527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13267, d113527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18643 q ha hb
  have h19 (q : Pattern) (ha : d113528 q = 1) (hb : d114677 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113528, d114677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113528, d114677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d113529 q = 1) (hb : d114678 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113529, d114678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113529, d114678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d113530 q = 1) (hb : d114679 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113530, d114679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d113530, d114679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d113531 q = 1) (hb : d114680 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113531, d114680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113531, d114680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113532 q = 1) (hb : d114681 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113532, d114681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113532, d114681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro18681 (p : Pattern) (ha : d113538 p = 1) (hb : d114687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113533 q = 1) (hb : d114682 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113533, d114682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113533, d114682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18680 q ha hb
  have h2 (q : Pattern) (ha : d113534 q = 1) (hb : d114683 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113534, d114683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113534, d114683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113535 q = 1) (hb : d114684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113535, d114684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113535, d114684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113536 q = 1) (hb : d114685 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113536, d114685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113536, d114685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113537 q = 1) (hb : d114686 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113537, d114686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113537, d114686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113538 q = 1) (hb : d114687 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113538, d114687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113538, d114687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18682 (p : Pattern) (ha : d13287 p = 1) (hb : d113547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1583 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1584 q = 1) (hb : d53025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1585 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1585, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1588 q = 1) (hb : d53029 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d53029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1588, d53029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13287 q = 1) (hb : d113547 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13287, d113547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13287, d113547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18683 (p : Pattern) (ha : d13297 p = 1) (hb : d113557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13288 q = 1) (hb : d113548 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13288, d113548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7962 q ha hb
    | true =>
      simp only [d13288, d113548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18682 q ha hb
  have h2 (q : Pattern) (ha : d13289 q = 1) (hb : d113549 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13289, d113549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13289, d113549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13290 q = 1) (hb : d113550 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13290, d113550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13290, d113550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13291 q = 1) (hb : d113551 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13291, d113551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13291, d113551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13296 q = 1) (hb : d113556 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13296, d113556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13296, d113556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13297 q = 1) (hb : d113557 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13297, d113557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13297, d113557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18684 (p : Pattern) (ha : d13307 p = 1) (hb : d113567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d113558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18683 q ha hb
    | true =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d113559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d113564 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d113564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d113564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d113565 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d113565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d113565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13306 q = 1) (hb : d113566 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13306, d113566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13306, d113566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13307 q = 1) (hb : d113567 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13307, d113567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13307, d113567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18685 (p : Pattern) (ha : d13317 p = 1) (hb : d113577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d113558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18683 q ha hb
    | true =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d113559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d113564 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d113564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d113564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d113565 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d113565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d113565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13306 q = 1) (hb : d113566 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13306, d113566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13306, d113566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13317 q = 1) (hb : d113577 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13317, d113577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13317, d113577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18686 (p : Pattern) (ha : d13466 p = 1) (hb : d113688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13455 q = 1) (hb : d113677 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13455, d113677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18684 q ha hb
    | true =>
      simp only [d13455, d113677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13456 q = 1) (hb : d113678 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13456, d113678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13456, d113678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13457 q = 1) (hb : d113679 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13457, d113679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13457, d113679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13458 q = 1) (hb : d113680 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13458, d113680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13458, d113680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13459 q = 1) (hb : d113681 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13459, d113681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13459, d113681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13461 q = 1) (hb : d113683 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13461, d113683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18685 q ha hb
    | true =>
      simp only [d13461, d113683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13462 q = 1) (hb : d113684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13462, d113684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13462, d113684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13463 q = 1) (hb : d113685 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13463, d113685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13463, d113685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13464 q = 1) (hb : d113686 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13464, d113686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13464, d113686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13465 q = 1) (hb : d113687 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13465, d113687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13465, d113687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13466 q = 1) (hb : d113688 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13466, d113688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13466, d113688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18687 (p : Pattern) (ha : d13475 p = 1) (hb : d113697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13461 q = 1) (hb : d113683 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13461, d113683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18685 q ha hb
    | true =>
      simp only [d13461, d113683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13462 q = 1) (hb : d113684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13462, d113684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13462, d113684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13463 q = 1) (hb : d113685 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13463, d113685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13463, d113685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13464 q = 1) (hb : d113686 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13464, d113686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13464, d113686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13465 q = 1) (hb : d113687 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13465, d113687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13465, d113687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13475 q = 1) (hb : d113697 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13475, d113697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13475, d113697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18688 (p : Pattern) (ha : d13516 p = 1) (hb : d113738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1868 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
  have h2 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1869 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1583 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1870 q = 1) (hb : d53196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1870, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1871 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1871, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1877 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1877, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13516 q = 1) (hb : d113738 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13516, d113738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13516, d113738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18689 (p : Pattern) (ha : d13522 p = 1) (hb : d113744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13517 q = 1) (hb : d113739 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13517, d113739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10900 q ha hb
    | true =>
      simp only [d13517, d113739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18688 q ha hb
  have h2 (q : Pattern) (ha : d13518 q = 1) (hb : d113740 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13518, d113740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13518, d113740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13519 q = 1) (hb : d113741 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13519, d113741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13519, d113741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13520 q = 1) (hb : d113742 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13520, d113742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13520, d113742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13521 q = 1) (hb : d113743 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13521, d113743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13521, d113743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13522 q = 1) (hb : d113744 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13522, d113744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13522, d113744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18690 (p : Pattern) (ha : d13586 p = 1) (hb : d113763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13523 q = 1) (hb : d113745 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d113745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18689 q ha hb
    | true =>
      simp only [d13523, d113745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13524 q = 1) (hb : d113746 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d113746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d113746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13583 q = 1) (hb : d113760 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13583, d113760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13583, d113760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13584 q = 1) (hb : d113761 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13584, d113761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13584, d113761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13585 q = 1) (hb : d113762 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13585, d113762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13585, d113762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13586 q = 1) (hb : d113763 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13586, d113763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13586, d113763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18691 (p : Pattern) (ha : d13592 p = 1) (hb : d113782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13587 q = 1) (hb : d113777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13587, d113777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18690 q ha hb
    | true =>
      simp only [d13587, d113777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13588 q = 1) (hb : d113778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13588, d113778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13588, d113778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13589 q = 1) (hb : d113779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13589, d113779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13589, d113779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13590 q = 1) (hb : d113780 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13590, d113780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13590, d113780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13591 q = 1) (hb : d113781 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13591, d113781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13591, d113781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13592 q = 1) (hb : d113782 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13592, d113782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13592, d113782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18692 (p : Pattern) (ha : d13282 p = 1) (hb : d113542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1555 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1556 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1557 q = 1) (hb : d52998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1557, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1558 q = 1) (hb : d52999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1558, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1572 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1573 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1574 q = 1) (hb : d53015 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1574, d53015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1574, d53015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13282 q = 1) (hb : d113542 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13282, d113542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13282, d113542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro18693 (p : Pattern) (ha : d113553 p = 1) (hb : d114693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13283 q = 1) (hb : d113543 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d113543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18692 q ha hb
    | true =>
      simp only [d13283, d113543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7962 q ha hb
  have h2 (q : Pattern) (ha : d13284 q = 1) (hb : d113544 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d113544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d113544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13285 q = 1) (hb : d113545 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d113545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d113545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d69226 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69227 q = 1) (hb : d88794 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69227, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7962 q hb ha
    | true =>
      simp only [d69227, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69228 q = 1) (hb : d88795 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69228, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69228, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69229 q = 1) (hb : d88796 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69229, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69229, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113546 q = 1) (hb : d114691 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113546, d114691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113546, d114691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113551 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113552 q = 1) (hb : d114692 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113552, d114692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113552, d114692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113553 q = 1) (hb : d114693 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113553, d114693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113553, d114693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18694 (p : Pattern) (ha : d113563 p = 1) (hb : d114699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18693 q ha hb
    | true =>
      simp only [d113554, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d113558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18683 q ha hb
    | true =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d113559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113560 q = 1) (hb : d114696 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113560, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113560, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113561 q = 1) (hb : d114697 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113561, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113561, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113562 q = 1) (hb : d114698 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113562, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113562, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113563 q = 1) (hb : d114699 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113563, d114699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113563, d114699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18695 (p : Pattern) (ha : d113573 p = 1) (hb : d114705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113568 q = 1) (hb : d114700 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113568, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18694 q ha hb
    | true =>
      simp only [d113568, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18684 q hb ha
  have h2 (q : Pattern) (ha : d113569 q = 1) (hb : d114701 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113569, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113569, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113570 q = 1) (hb : d114702 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113570, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113570, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113571 q = 1) (hb : d114703 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113571, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113571, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113572 q = 1) (hb : d114704 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113572, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113572, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113573 q = 1) (hb : d114705 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113573, d114705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113573, d114705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18696 (p : Pattern) (ha : d113576 p = 1) (hb : d114708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18693 q ha hb
    | true =>
      simp only [d113554, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d113558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18683 q ha hb
    | true =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d113559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113560 q = 1) (hb : d114696 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113560, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113560, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113561 q = 1) (hb : d114697 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113561, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113561, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113562 q = 1) (hb : d114698 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113562, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113562, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113576 q = 1) (hb : d114708 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113576, d114708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113576, d114708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18697 (p : Pattern) (ha : d113583 p = 1) (hb : d114714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113568 q = 1) (hb : d114700 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113568, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18694 q ha hb
    | true =>
      simp only [d113568, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18684 q hb ha
  have h2 (q : Pattern) (ha : d113569 q = 1) (hb : d114701 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113569, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113569, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113570 q = 1) (hb : d114702 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113570, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113570, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113571 q = 1) (hb : d114703 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113571, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113571, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113572 q = 1) (hb : d114704 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113572, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113572, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113578 q = 1) (hb : d114709 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113578, d114709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18696 q ha hb
    | true =>
      simp only [d113578, d114709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18685 q hb ha
  have h7 (q : Pattern) (ha : d113579 q = 1) (hb : d114710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113579, d114710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113579, d114710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113580 q = 1) (hb : d114711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113580, d114711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113580, d114711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113581 q = 1) (hb : d114712 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113581, d114712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113581, d114712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113582 q = 1) (hb : d114713 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113582, d114713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113582, d114713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113583 q = 1) (hb : d114714 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113583, d114714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113583, d114714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18698 (p : Pattern) (ha : d13330 p = 1) (hb : d113590 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d113558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18683 q ha hb
    | true =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d113559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d113564 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d113564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d113564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d113565 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d113565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d113565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13329 q = 1) (hb : d113589 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13329, d113589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13329, d113589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13330 q = 1) (hb : d113590 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13330, d113590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13330, d113590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18699 (p : Pattern) (ha : d13340 p = 1) (hb : d113600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d113558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18683 q ha hb
    | true =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d113559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d113564 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d113564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d113564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13338 q = 1) (hb : d113598 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13338, d113598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13338, d113598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13339 q = 1) (hb : d113599 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13339, d113599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13339, d113599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13340 q = 1) (hb : d113600 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13340, d113600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13340, d113600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18700 (p : Pattern) (ha : d113588 p = 1) (hb : d114719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18693 q ha hb
    | true =>
      simp only [d113554, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d113558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18683 q ha hb
    | true =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d113559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113560 q = 1) (hb : d114696 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113560, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113560, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113561 q = 1) (hb : d114697 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113561, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113561, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113587 q = 1) (hb : d114718 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113587, d114718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113587, d114718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113588 q = 1) (hb : d114719 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113588, d114719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113588, d114719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18701 (p : Pattern) (ha : d113597 p = 1) (hb : d114726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18693 q ha hb
    | true =>
      simp only [d113554, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d113558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18683 q ha hb
    | true =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d113559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113560 q = 1) (hb : d114696 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113560, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113560, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113595 q = 1) (hb : d114724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113595, d114724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113595, d114724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113596 q = 1) (hb : d114725 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113596, d114725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113596, d114725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113597 q = 1) (hb : d114726 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113597, d114726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113597, d114726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18702 (p : Pattern) (ha : d13344 p = 1) (hb : d113604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1665 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
    | true =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1666 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1667 q = 1) (hb : d53108 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1667, d53108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1667, d53108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1668 q = 1) (hb : d53109 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1668, d53109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1668, d53109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1555 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1556 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1557 q = 1) (hb : d52998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1557, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1558 q = 1) (hb : d52999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1558, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1669 q = 1) (hb : d53110 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1669, d53110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1669, d53110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13344 q = 1) (hb : d113604 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13344, d113604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13344, d113604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro18703 (p : Pattern) (ha : d113622 p = 1) (hb : d114735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13345 q = 1) (hb : d113605 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13345, d113605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18702 q ha hb
    | true =>
      simp only [d13345, d113605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18692 q ha hb
  have h2 (q : Pattern) (ha : d13346 q = 1) (hb : d113606 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13346, d113606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13346, d113606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13347 q = 1) (hb : d113607 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13347, d113607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13347, d113607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113616 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113617 q = 1) (hb : d114730 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113617, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18692 q hb ha
    | true =>
      simp only [d113617, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113618 q = 1) (hb : d114731 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113618, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113618, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113619 q = 1) (hb : d114732 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113619, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113619, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113620 q = 1) (hb : d114733 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113620, d114733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113620, d114733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113546 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113621 q = 1) (hb : d114734 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113621, d114734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113621, d114734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113622 q = 1) (hb : d114735 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113622, d114735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113622, d114735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18704 (p : Pattern) (ha : d113626 p = 1) (hb : d114693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13283 q = 1) (hb : d113543 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d113543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18692 q ha hb
    | true =>
      simp only [d13283, d113543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7962 q ha hb
  have h2 (q : Pattern) (ha : d13284 q = 1) (hb : d113544 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d113544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d113544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13285 q = 1) (hb : d113545 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d113545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d113545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d69226 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69227 q = 1) (hb : d88794 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69227, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7962 q hb ha
    | true =>
      simp only [d69227, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69228 q = 1) (hb : d88795 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69228, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69228, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69229 q = 1) (hb : d88796 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69229, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69229, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113546 q = 1) (hb : d114691 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113546, d114691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113546, d114691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d69230 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113625 q = 1) (hb : d114692 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113625, d114692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113625, d114692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113626 q = 1) (hb : d114693 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113626, d114693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113626, d114693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18705 (p : Pattern) (ha : d113632 p = 1) (hb : d114741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113623 q = 1) (hb : d114736 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113623, d114736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18703 q ha hb
    | true =>
      simp only [d113623, d114736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113624 q = 1) (hb : d114737 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113624, d114737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113624, d114737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113627 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113627, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18704 q ha hb
    | true =>
      simp only [d113627, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113628 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113628, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113628, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113629 q = 1) (hb : d114738 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113629, d114738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113629, d114738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113630 q = 1) (hb : d114739 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113630, d114739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113630, d114739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113631 q = 1) (hb : d114740 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113631, d114740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113631, d114740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113632 q = 1) (hb : d114741 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113632, d114741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113632, d114741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18706 (p : Pattern) (ha : d113636 p = 1) (hb : d114699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113627 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113627, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18704 q ha hb
    | true =>
      simp only [d113627, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113628 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113628, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113628, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d113558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18683 q ha hb
    | true =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d113559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113633 q = 1) (hb : d114696 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113633, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113633, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113634 q = 1) (hb : d114697 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113634, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113634, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113635 q = 1) (hb : d114698 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113635, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113635, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113636 q = 1) (hb : d114699 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113636, d114699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113636, d114699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18707 (p : Pattern) (ha : d113642 p = 1) (hb : d114747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18693 q ha hb
    | true =>
      simp only [d113554, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113639 q = 1) (hb : d114744 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113639, d114744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113639, d114744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113640 q = 1) (hb : d114745 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113640, d114745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113640, d114745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113641 q = 1) (hb : d114746 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113641, d114746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113641, d114746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113642 q = 1) (hb : d114747 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113642, d114747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113642, d114747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18708 (p : Pattern) (ha : d113648 p = 1) (hb : d114753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113591 q = 1) (hb : d114720 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113591, d114720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18700 q ha hb
    | true =>
      simp only [d113591, d114720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18698 q hb ha
  have h2 (q : Pattern) (ha : d113592 q = 1) (hb : d114721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113592, d114721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113592, d114721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113593 q = 1) (hb : d114722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113593, d114722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113593, d114722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113594 q = 1) (hb : d114723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113594, d114723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113594, d114723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113601 q = 1) (hb : d114727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113601, d114727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18701 q ha hb
    | true =>
      simp only [d113601, d114727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18699 q hb ha
  have h6 (q : Pattern) (ha : d113602 q = 1) (hb : d114728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113602, d114728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113602, d114728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113603 q = 1) (hb : d114729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113603, d114729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113603, d114729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113637 q = 1) (hb : d114742 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113637, d114742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18705 q ha hb
    | true =>
      simp only [d113637, d114742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18706 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113568 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113638 q = 1) (hb : d114743 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113638, d114743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113638, d114743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113643 q = 1) (hb : d114748 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113643, d114748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18707 q ha hb
    | true =>
      simp only [d113643, d114748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113644 q = 1) (hb : d114749 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113644, d114749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113644, d114749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113645 q = 1) (hb : d114750 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113645, d114750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113645, d114750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113646 q = 1) (hb : d114751 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113646, d114751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113646, d114751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113647 q = 1) (hb : d114752 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113647, d114752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113647, d114752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113648 q = 1) (hb : d114753 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113648, d114753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113648, d114753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro18709 (p : Pattern) (ha : d13425 p = 1) (hb : d113650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d113558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18683 q ha hb
    | true =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d113559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d113564 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d113564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d113564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d113565 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d113565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d113565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13329 q = 1) (hb : d113589 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13329, d113589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13329, d113589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13425 q = 1) (hb : d113650 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13425, d113650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13425, d113650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18710 (p : Pattern) (ha : d13431 p = 1) (hb : d113656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d113558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18683 q ha hb
    | true =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d113559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d113564 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d113564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d113564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13338 q = 1) (hb : d113598 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13338, d113598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13338, d113598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13339 q = 1) (hb : d113599 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13339, d113599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13339, d113599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13431 q = 1) (hb : d113656 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13431, d113656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13431, d113656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18711 (p : Pattern) (ha : d113649 p = 1) (hb : d114754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18693 q ha hb
    | true =>
      simp only [d113554, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d113558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18683 q ha hb
    | true =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d113559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113560 q = 1) (hb : d114696 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113560, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113560, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113561 q = 1) (hb : d114697 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113561, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113561, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113587 q = 1) (hb : d114718 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113587, d114718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113587, d114718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113649 q = 1) (hb : d114754 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113649, d114754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113649, d114754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18712 (p : Pattern) (ha : d113655 p = 1) (hb : d114759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18693 q ha hb
    | true =>
      simp only [d113554, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d113558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18683 q ha hb
    | true =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d113559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113560 q = 1) (hb : d114696 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113560, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113560, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113595 q = 1) (hb : d114724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113595, d114724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113595, d114724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113596 q = 1) (hb : d114725 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113596, d114725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113596, d114725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113655 q = 1) (hb : d114759 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113655, d114759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113655, d114759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18713 (p : Pattern) (ha : d113660 p = 1) (hb : d114763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113623 q = 1) (hb : d114736 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113623, d114736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18703 q ha hb
    | true =>
      simp only [d113623, d114736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113624 q = 1) (hb : d114737 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113624, d114737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113624, d114737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113627 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113627, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18704 q ha hb
    | true =>
      simp only [d113627, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113628 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113628, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113628, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113629 q = 1) (hb : d114738 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113629, d114738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113629, d114738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113630 q = 1) (hb : d114739 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113630, d114739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113630, d114739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113631 q = 1) (hb : d114740 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113631, d114740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113631, d114740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113660 q = 1) (hb : d114763 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113660, d114763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113660, d114763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18714 (p : Pattern) (ha : d113661 p = 1) (hb : d114708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113627 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113627, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18704 q ha hb
    | true =>
      simp only [d113627, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113628 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113628, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113628, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d113558 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18683 q ha hb
    | true =>
      simp only [d13298, d113558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d113559 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d113559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113633 q = 1) (hb : d114696 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113633, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113633, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113634 q = 1) (hb : d114697 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113634, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113634, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113635 q = 1) (hb : d114698 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113635, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113635, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113661 q = 1) (hb : d114708 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113661, d114708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113661, d114708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18715 (p : Pattern) (ha : d113664 p = 1) (hb : d114766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18693 q ha hb
    | true =>
      simp only [d113554, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113639 q = 1) (hb : d114744 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113639, d114744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113639, d114744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113640 q = 1) (hb : d114745 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113640, d114745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113640, d114745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113641 q = 1) (hb : d114746 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113641, d114746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113641, d114746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113664 q = 1) (hb : d114766 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113664, d114766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113664, d114766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro18716 (p : Pattern) (ha : d113670 p = 1) (hb : d114772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113591 q = 1) (hb : d114720 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113591, d114720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18700 q ha hb
    | true =>
      simp only [d113591, d114720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18698 q hb ha
  have h2 (q : Pattern) (ha : d113592 q = 1) (hb : d114721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113592, d114721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113592, d114721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113593 q = 1) (hb : d114722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113593, d114722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113593, d114722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113594 q = 1) (hb : d114723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113594, d114723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113594, d114723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113601 q = 1) (hb : d114727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113601, d114727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18701 q ha hb
    | true =>
      simp only [d113601, d114727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18699 q hb ha
  have h6 (q : Pattern) (ha : d113602 q = 1) (hb : d114728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113602, d114728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113602, d114728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113603 q = 1) (hb : d114729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113603, d114729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113603, d114729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113637 q = 1) (hb : d114742 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113637, d114742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18705 q ha hb
    | true =>
      simp only [d113637, d114742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18706 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113568 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113638 q = 1) (hb : d114743 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113638, d114743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113638, d114743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113643 q = 1) (hb : d114748 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113643, d114748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18707 q ha hb
    | true =>
      simp only [d113643, d114748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113644 q = 1) (hb : d114749 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113644, d114749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113644, d114749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113645 q = 1) (hb : d114750 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113645, d114750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113645, d114750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113646 q = 1) (hb : d114751 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113646, d114751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113646, d114751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113647 q = 1) (hb : d114752 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113647, d114752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113647, d114752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113651 q = 1) (hb : d114755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113651, d114755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18711 q ha hb
    | true =>
      simp only [d113651, d114755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18709 q hb ha
  have h17 (q : Pattern) (ha : d113652 q = 1) (hb : d114756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113652, d114756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113652, d114756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113653 q = 1) (hb : d114757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113653, d114757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113653, d114757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d113654 q = 1) (hb : d114758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113654, d114758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113654, d114758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113657 q = 1) (hb : d114760 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113657, d114760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18712 q ha hb
    | true =>
      simp only [d113657, d114760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18710 q hb ha
  have h21 (q : Pattern) (ha : d113658 q = 1) (hb : d114761 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113658, d114761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113658, d114761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d113659 q = 1) (hb : d114762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113659, d114762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113659, d114762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113662 q = 1) (hb : d114764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113662, d114764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18713 q ha hb
    | true =>
      simp only [d113662, d114764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18714 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d113578 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d113663 q = 1) (hb : d114765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113663, d114765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d113663, d114765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d113665 q = 1) (hb : d114767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113665, d114767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18715 q ha hb
    | true =>
      simp only [d113665, d114767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d113666 q = 1) (hb : d114768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113666, d114768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d113666, d114768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d113667 q = 1) (hb : d114769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113667, d114769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d113667, d114769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d113668 q = 1) (hb : d114770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113668, d114770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d113668, d114770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d113669 q = 1) (hb : d114771 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113669, d114771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113669, d114771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d113670 q = 1) (hb : d114772 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113670, d114772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113670, d114772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro18717 (p : Pattern) (ha : d113682 p = 1) (hb : d114774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113672 q = 1) (hb : d114700 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113672, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18706 q ha hb
    | true =>
      simp only [d113672, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18684 q hb ha
  have h2 (q : Pattern) (ha : d113673 q = 1) (hb : d114701 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113673, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113673, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113674 q = 1) (hb : d114702 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113674, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113674, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113675 q = 1) (hb : d114703 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113675, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113675, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113676 q = 1) (hb : d114704 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113676, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113676, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13455 q = 1) (hb : d113677 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13455, d113677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18684 q ha hb
    | true =>
      simp only [d13455, d113677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13456 q = 1) (hb : d113678 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13456, d113678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13456, d113678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13457 q = 1) (hb : d113679 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13457, d113679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13457, d113679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13458 q = 1) (hb : d113680 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13458, d113680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13458, d113680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13459 q = 1) (hb : d113681 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13459, d113681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13459, d113681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113682 q = 1) (hb : d114774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113682, d114774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113682, d114774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro18718 (p : Pattern) (ha : d113695 p = 1) (hb : d114781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113662 q = 1) (hb : d114764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113662, d114764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18713 q ha hb
    | true =>
      simp only [d113662, d114764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18714 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113578 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113663 q = 1) (hb : d114765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113663, d114765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113663, d114765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113665 q = 1) (hb : d114767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113665, d114767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18715 q ha hb
    | true =>
      simp only [d113665, d114767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113666 q = 1) (hb : d114768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113666, d114768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113666, d114768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113667 q = 1) (hb : d114769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113667, d114769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113667, d114769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113693 q = 1) (hb : d114779 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113693, d114779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113693, d114779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113694 q = 1) (hb : d114780 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113694, d114780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113694, d114780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113695 q = 1) (hb : d114781 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113695, d114781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113695, d114781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro18719 (p : Pattern) (ha : d13481 p = 1) (hb : d113703 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d1857 q = 1) (hb : d53183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
  have h8 (q : Pattern) (ha : d1555 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1858 q = 1) (hb : d53184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1858, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1556 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1859 q = 1) (hb : d53185 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1859, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1860 q = 1) (hb : d53186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1860, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1861 q = 1) (hb : d53187 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1861, d53187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1861, d53187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13481 q = 1) (hb : d113703 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13481, d113703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13481, d113703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro18720 (p : Pattern) (ha : d13482 p = 1) (hb : d113704 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d1862 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
  have h8 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1863 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1864 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1865 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1865, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1866 q = 1) (hb : d53192 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1866, d53192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1866, d53192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13482 q = 1) (hb : d113704 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13482, d113704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13482, d113704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro18721 (p : Pattern) (ha : d113727 p = 1) (hb : d114792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13483 q = 1) (hb : d113705 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13483, d113705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18719 q ha hb
    | true =>
      simp only [d13483, d113705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18720 q ha hb
  have h2 (q : Pattern) (ha : d13484 q = 1) (hb : d113706 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13484, d113706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13484, d113706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13485 q = 1) (hb : d113707 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13485, d113707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13485, d113707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113717 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113718 q = 1) (hb : d114787 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113718, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18720 q hb ha
    | true =>
      simp only [d113718, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113719 q = 1) (hb : d114788 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113719, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113719, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113720 q = 1) (hb : d114789 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113720, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113720, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113721 q = 1) (hb : d114790 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113721, d114790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113721, d114790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113725 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113726 q = 1) (hb : d114791 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113726, d114791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113726, d114791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113727 q = 1) (hb : d114792 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113727, d114792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113727, d114792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18722 (p : Pattern) (ha : d113731 p = 1) (hb : d114797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13500 q = 1) (hb : d113722 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13500, d113722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18720 q ha hb
    | true =>
      simp only [d13500, d113722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10900 q ha hb
  have h2 (q : Pattern) (ha : d13501 q = 1) (hb : d113723 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13501, d113723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13501, d113723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13502 q = 1) (hb : d113724 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13502, d113724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13502, d113724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76230 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76231 q = 1) (hb : d88858 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76231, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10900 q hb ha
    | true =>
      simp only [d76231, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76232 q = 1) (hb : d88859 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76232, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76232, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76233 q = 1) (hb : d88860 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76233, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76233, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113725 q = 1) (hb : d114795 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113725, d114795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113725, d114795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d76234 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113730 q = 1) (hb : d114796 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113730, d114796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113730, d114796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113731 q = 1) (hb : d114797 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113731, d114797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113731, d114797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18723 (p : Pattern) (ha : d113737 p = 1) (hb : d114803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113728 q = 1) (hb : d114793 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113728, d114793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18721 q ha hb
    | true =>
      simp only [d113728, d114793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113729 q = 1) (hb : d114794 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113729, d114794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113729, d114794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113732 q = 1) (hb : d114798 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113732, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18722 q ha hb
    | true =>
      simp only [d113732, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113733 q = 1) (hb : d114799 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113733, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113733, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113734 q = 1) (hb : d114800 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113734, d114800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113734, d114800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113735 q = 1) (hb : d114801 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113735, d114801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113735, d114801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113736 q = 1) (hb : d114802 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113736, d114802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113736, d114802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113737 q = 1) (hb : d114803 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113737, d114803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113737, d114803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18724 (p : Pattern) (ha : d113750 p = 1) (hb : d114807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113732 q = 1) (hb : d114798 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113732, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18722 q ha hb
    | true =>
      simp only [d113732, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113733 q = 1) (hb : d114799 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113733, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113733, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13523 q = 1) (hb : d113745 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d113745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18689 q ha hb
    | true =>
      simp only [d13523, d113745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13524 q = 1) (hb : d113746 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d113746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d113746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113747 q = 1) (hb : d114804 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113747, d114804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113747, d114804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113748 q = 1) (hb : d114805 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113748, d114805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113748, d114805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113749 q = 1) (hb : d114806 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113749, d114806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113749, d114806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113750 q = 1) (hb : d114807 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113750, d114807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113750, d114807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18725 (p : Pattern) (ha : d113753 p = 1) (hb : d114797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13500 q = 1) (hb : d113722 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13500, d113722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18720 q ha hb
    | true =>
      simp only [d13500, d113722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10900 q ha hb
  have h2 (q : Pattern) (ha : d13501 q = 1) (hb : d113723 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13501, d113723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13501, d113723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13502 q = 1) (hb : d113724 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13502, d113724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13502, d113724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76230 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76231 q = 1) (hb : d88858 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76231, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10900 q hb ha
    | true =>
      simp only [d76231, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76232 q = 1) (hb : d88859 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76232, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76232, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76233 q = 1) (hb : d88860 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76233, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76233, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113725 q = 1) (hb : d114795 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113725, d114795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113725, d114795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113742 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113752 q = 1) (hb : d114796 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113752, d114796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113752, d114796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113753 q = 1) (hb : d114797 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113753, d114797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113753, d114797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18726 (p : Pattern) (ha : d113769 p = 1) (hb : d114813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113754 q = 1) (hb : d114798 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113754, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18725 q ha hb
    | true =>
      simp only [d113754, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113755 q = 1) (hb : d114799 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113755, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113755, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113766 q = 1) (hb : d114810 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113766, d114810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113766, d114810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113767 q = 1) (hb : d114811 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113767, d114811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113767, d114811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113768 q = 1) (hb : d114812 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113768, d114812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113768, d114812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113769 q = 1) (hb : d114813 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113769, d114813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113769, d114813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro18727 (p : Pattern) (ha : d113775 p = 1) (hb : d114819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113751 q = 1) (hb : d114808 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113751, d114808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18723 q ha hb
    | true =>
      simp only [d113751, d114808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18724 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113765 q = 1) (hb : d114809 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113765, d114809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113765, d114809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113770 q = 1) (hb : d114814 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113770, d114814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18726 q ha hb
    | true =>
      simp only [d113770, d114814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113771 q = 1) (hb : d114815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113771, d114815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113771, d114815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113772 q = 1) (hb : d114816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113772, d114816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113772, d114816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113773 q = 1) (hb : d114817 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113773, d114817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113773, d114817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113774 q = 1) (hb : d114818 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113774, d114818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113774, d114818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113775 q = 1) (hb : d114819 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113775, d114819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113775, d114819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro18728 (p : Pattern) (ha : d113788 p = 1) (hb : d114825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113574 q = 1) (hb : d114706 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113574, d114706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113574, d114706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18695 q ha hb
  have h2 (q : Pattern) (ha : d113575 q = 1) (hb : d114707 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113575, d114707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113575, d114707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d113584 q = 1) (hb : d114715 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113584, d114715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18695 q ha hb
    | true =>
      simp only [d113584, d114715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18697 q ha hb
  have h4 (q : Pattern) (ha : d113585 q = 1) (hb : d114716 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113585, d114716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113585, d114716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113586 q = 1) (hb : d114717 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113586, d114717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113586, d114717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113671 q = 1) (hb : d114773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113671, d114773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18708 q ha hb
    | true =>
      simp only [d113671, d114773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18716 q ha hb
  have h7 (q : Pattern) (ha : d113689 q = 1) (hb : d114775 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113689, d114775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18717 q ha hb
    | true =>
      simp only [d113689, d114775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18686 q hb ha
  have h8 (q : Pattern) (ha : d113690 q = 1) (hb : d114776 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113690, d114776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113690, d114776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113691 q = 1) (hb : d114777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113691, d114777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113691, d114777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d113692 q = 1) (hb : d114778 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113692, d114778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113692, d114778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113696 q = 1) (hb : d114782 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113696, d114782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113696, d114782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18718 q ha hb
  have h12 (q : Pattern) (ha : d13476 q = 1) (hb : d113698 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13476, d113698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13476, d113698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18687 q ha hb
  have h13 (q : Pattern) (ha : d113699 q = 1) (hb : d114783 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113699, d114783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113699, d114783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d113700 q = 1) (hb : d114784 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113700, d114784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113700, d114784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d113701 q = 1) (hb : d114785 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113701, d114785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d113701, d114785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d113702 q = 1) (hb : d114786 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113702, d114786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113702, d114786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113776 q = 1) (hb : d114820 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113776, d114820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113776, d114820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18727 q ha hb
  have h18 (q : Pattern) (ha : d13593 q = 1) (hb : d113783 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13593, d113783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13593, d113783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18691 q ha hb
  have h19 (q : Pattern) (ha : d113784 q = 1) (hb : d114821 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113784, d114821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113784, d114821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d113785 q = 1) (hb : d114822 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113785, d114822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113785, d114822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d113786 q = 1) (hb : d114823 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113786, d114823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d113786, d114823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d113787 q = 1) (hb : d114824 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113787, d114824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113787, d114824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113788 q = 1) (hb : d114825 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113788, d114825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113788, d114825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro18729 (p : Pattern) (ha : d113794 p = 1) (hb : d114831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113789 q = 1) (hb : d114826 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113789, d114826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113789, d114826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18728 q ha hb
  have h2 (q : Pattern) (ha : d113790 q = 1) (hb : d114827 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113790, d114827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113790, d114827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113791 q = 1) (hb : d114828 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113791, d114828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113791, d114828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113792 q = 1) (hb : d114829 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113792, d114829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113792, d114829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113793 q = 1) (hb : d114830 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113793, d114830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113793, d114830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113794 q = 1) (hb : d114831 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113794, d114831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113794, d114831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18730 (p : Pattern) (ha : d13614 p = 1) (hb : d113804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2066 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2067 q = 1) (hb : d53346 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2068 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2071 q = 1) (hb : d53350 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, d53350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2071, d53350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13614 q = 1) (hb : d113804 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13614, d113804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13614, d113804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18731 (p : Pattern) (ha : d13624 p = 1) (hb : d113814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13615 q = 1) (hb : d113805 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13615, d113805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7979 q ha hb
    | true =>
      simp only [d13615, d113805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18730 q ha hb
  have h2 (q : Pattern) (ha : d13616 q = 1) (hb : d113806 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13616, d113806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13616, d113806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13617 q = 1) (hb : d113807 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13617, d113807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13617, d113807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13618 q = 1) (hb : d113808 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13618, d113808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13618, d113808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13623 q = 1) (hb : d113813 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13623, d113813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13623, d113813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13624 q = 1) (hb : d113814 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13624, d113814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13624, d113814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18732 (p : Pattern) (ha : d13634 p = 1) (hb : d113824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d113815 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d113815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18731 q ha hb
    | true =>
      simp only [d13625, d113815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d113816 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d113816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d113816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d113821 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d113821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d113821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d113822 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, d113822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, d113822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13633 q = 1) (hb : d113823 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13633, d113823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13633, d113823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13634 q = 1) (hb : d113824 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13634, d113824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13634, d113824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18733 (p : Pattern) (ha : d13644 p = 1) (hb : d113834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d113815 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d113815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18731 q ha hb
    | true =>
      simp only [d13625, d113815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d113816 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d113816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d113816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d113821 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d113821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d113821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d113822 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, d113822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, d113822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13633 q = 1) (hb : d113823 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13633, d113823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13633, d113823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13644 q = 1) (hb : d113834 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13644, d113834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13644, d113834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18734 (p : Pattern) (ha : d13793 p = 1) (hb : d113945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13782 q = 1) (hb : d113934 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13782, d113934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18732 q ha hb
    | true =>
      simp only [d13782, d113934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13783 q = 1) (hb : d113935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13783, d113935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13783, d113935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13784 q = 1) (hb : d113936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13784, d113936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13784, d113936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13785 q = 1) (hb : d113937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13785, d113937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13785, d113937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13786 q = 1) (hb : d113938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13786, d113938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13786, d113938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13788 q = 1) (hb : d113940 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13788, d113940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18733 q ha hb
    | true =>
      simp only [d13788, d113940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13789 q = 1) (hb : d113941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13789, d113941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13789, d113941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13790 q = 1) (hb : d113942 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13790, d113942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13790, d113942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13791 q = 1) (hb : d113943 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13791, d113943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13791, d113943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13792 q = 1) (hb : d113944 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13792, d113944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13792, d113944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13793 q = 1) (hb : d113945 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13793, d113945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13793, d113945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18735 (p : Pattern) (ha : d13802 p = 1) (hb : d113954 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13788 q = 1) (hb : d113940 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13788, d113940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18733 q ha hb
    | true =>
      simp only [d13788, d113940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13789 q = 1) (hb : d113941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13789, d113941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13789, d113941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13790 q = 1) (hb : d113942 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13790, d113942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13790, d113942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13791 q = 1) (hb : d113943 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13791, d113943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13791, d113943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13792 q = 1) (hb : d113944 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13792, d113944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13792, d113944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13802 q = 1) (hb : d113954 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13802, d113954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13802, d113954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18736 (p : Pattern) (ha : d13843 p = 1) (hb : d113995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2346 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
  have h2 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2347 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2066 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2348 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2349 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2349, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2355 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2355, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13843 q = 1) (hb : d113995 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13843, d113995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13843, d113995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18737 (p : Pattern) (ha : d13849 p = 1) (hb : d114001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13844 q = 1) (hb : d113996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13844, d113996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10914 q ha hb
    | true =>
      simp only [d13844, d113996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18736 q ha hb
  have h2 (q : Pattern) (ha : d13845 q = 1) (hb : d113997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13845, d113997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13845, d113997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13846 q = 1) (hb : d113998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13846, d113998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13846, d113998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13847 q = 1) (hb : d113999 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13847, d113999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13847, d113999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13848 q = 1) (hb : d114000 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13848, d114000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13848, d114000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13849 q = 1) (hb : d114001 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13849, d114001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13849, d114001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18738 (p : Pattern) (ha : d13913 p = 1) (hb : d114020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13850 q = 1) (hb : d114002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, d114002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18737 q ha hb
    | true =>
      simp only [d13850, d114002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13851 q = 1) (hb : d114003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, d114003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, d114003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13910 q = 1) (hb : d114017 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13910, d114017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13910, d114017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13911 q = 1) (hb : d114018 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13911, d114018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13911, d114018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13912 q = 1) (hb : d114019 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13912, d114019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13912, d114019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13913 q = 1) (hb : d114020 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13913, d114020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13913, d114020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18739 (p : Pattern) (ha : d13919 p = 1) (hb : d114039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13914 q = 1) (hb : d114034 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13914, d114034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18738 q ha hb
    | true =>
      simp only [d13914, d114034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13915 q = 1) (hb : d114035 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13915, d114035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13915, d114035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13916 q = 1) (hb : d114036 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13916, d114036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13916, d114036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13917 q = 1) (hb : d114037 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13917, d114037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13917, d114037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13918 q = 1) (hb : d114038 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13918, d114038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13918, d114038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13919 q = 1) (hb : d114039 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13919, d114039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13919, d114039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18740 (p : Pattern) (ha : d13609 p = 1) (hb : d113799 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2055 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2056 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2057 q = 1) (hb : d53336 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2057, d53336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2057, d53336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13609 q = 1) (hb : d113799 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13609, d113799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13609, d113799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro18741 (p : Pattern) (ha : d113810 p = 1) (hb : d114838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13610 q = 1) (hb : d113800 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13610, d113800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18740 q ha hb
    | true =>
      simp only [d13610, d113800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7979 q ha hb
  have h2 (q : Pattern) (ha : d13611 q = 1) (hb : d113801 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13611, d113801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13611, d113801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13612 q = 1) (hb : d113802 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13612, d113802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13612, d113802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d69336 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69337 q = 1) (hb : d88948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69337, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7979 q hb ha
    | true =>
      simp only [d69337, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69338 q = 1) (hb : d88949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69338, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69338, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69339 q = 1) (hb : d88950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69339, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69339, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113803 q = 1) (hb : d114836 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113803, d114836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113803, d114836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113808 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113809 q = 1) (hb : d114837 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113809, d114837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113809, d114837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113810 q = 1) (hb : d114838 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113810, d114838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113810, d114838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro18742 (p : Pattern) (ha : d113820 p = 1) (hb : d114844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d114839 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18741 q ha hb
    | true =>
      simp only [d113811, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d114840 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d113815 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d113815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18731 q ha hb
    | true =>
      simp only [d13625, d113815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d113816 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d113816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d113816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d114841 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113818 q = 1) (hb : d114842 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113818, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113818, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113819 q = 1) (hb : d114843 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113819, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113819, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113820 q = 1) (hb : d114844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113820, d114844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113820, d114844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18743 (p : Pattern) (ha : d113830 p = 1) (hb : d114850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113825 q = 1) (hb : d114845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113825, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18742 q ha hb
    | true =>
      simp only [d113825, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18732 q hb ha
  have h2 (q : Pattern) (ha : d113826 q = 1) (hb : d114846 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113826, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113826, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113827 q = 1) (hb : d114847 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113827, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113827, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113828 q = 1) (hb : d114848 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113828, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113828, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113829 q = 1) (hb : d114849 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113829, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113829, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113830 q = 1) (hb : d114850 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113830, d114850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113830, d114850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18744 (p : Pattern) (ha : d113833 p = 1) (hb : d114853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d114839 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18741 q ha hb
    | true =>
      simp only [d113811, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d114840 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d113815 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d113815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18731 q ha hb
    | true =>
      simp only [d13625, d113815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d113816 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d113816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d113816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d114841 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113818 q = 1) (hb : d114842 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113818, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113818, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113819 q = 1) (hb : d114843 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113819, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113819, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113833 q = 1) (hb : d114853 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113833, d114853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113833, d114853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro18745 (p : Pattern) (ha : d113840 p = 1) (hb : d114859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113825 q = 1) (hb : d114845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113825, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18742 q ha hb
    | true =>
      simp only [d113825, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18732 q hb ha
  have h2 (q : Pattern) (ha : d113826 q = 1) (hb : d114846 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113826, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113826, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113827 q = 1) (hb : d114847 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113827, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113827, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113828 q = 1) (hb : d114848 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113828, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113828, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113829 q = 1) (hb : d114849 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113829, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113829, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113835 q = 1) (hb : d114854 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113835, d114854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18744 q ha hb
    | true =>
      simp only [d113835, d114854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18733 q hb ha
  have h7 (q : Pattern) (ha : d113836 q = 1) (hb : d114855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113836, d114855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113836, d114855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113837 q = 1) (hb : d114856 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113837, d114856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113837, d114856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113838 q = 1) (hb : d114857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113838, d114857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113838, d114857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113839 q = 1) (hb : d114858 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113839, d114858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113839, d114858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113840 q = 1) (hb : d114859 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113840, d114859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113840, d114859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18746 (p : Pattern) (ha : d13657 p = 1) (hb : d113847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d113815 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d113815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18731 q ha hb
    | true =>
      simp only [d13625, d113815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d113816 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d113816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d113816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d113821 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d113821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d113821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d113822 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, d113822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, d113822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13656 q = 1) (hb : d113846 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13656, d113846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13656, d113846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13657 q = 1) (hb : d113847 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13657, d113847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13657, d113847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18747 (p : Pattern) (ha : d13667 p = 1) (hb : d113857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d113815 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d113815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18731 q ha hb
    | true =>
      simp only [d13625, d113815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d113816 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d113816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d113816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d113821 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d113821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d113821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13665 q = 1) (hb : d113855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13665, d113855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13665, d113855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13666 q = 1) (hb : d113856 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13666, d113856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13666, d113856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13667 q = 1) (hb : d113857 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13667, d113857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13667, d113857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18748 (p : Pattern) (ha : d113845 p = 1) (hb : d114864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d114839 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18741 q ha hb
    | true =>
      simp only [d113811, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d114840 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d113815 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d113815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18731 q ha hb
    | true =>
      simp only [d13625, d113815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d113816 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d113816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d113816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d114841 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113818 q = 1) (hb : d114842 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113818, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113818, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113844 q = 1) (hb : d114863 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113844, d114863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113844, d114863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113845 q = 1) (hb : d114864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113845, d114864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113845, d114864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18749 (p : Pattern) (ha : d113854 p = 1) (hb : d114871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d114839 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18741 q ha hb
    | true =>
      simp only [d113811, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d114840 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d113815 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d113815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18731 q ha hb
    | true =>
      simp only [d13625, d113815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d113816 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d113816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d113816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d114841 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113852 q = 1) (hb : d114869 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113852, d114869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113852, d114869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113853 q = 1) (hb : d114870 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113853, d114870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113853, d114870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113854 q = 1) (hb : d114871 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113854, d114871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113854, d114871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
