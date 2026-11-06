import NetHack.Soko22Hazard87.EqIntroBlocks0156
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro39250 (p : Pattern) (selected : d371988 p = 1) : d375431 p = 1 := by
  have h0 (q : Pattern) (selected : d371795 q = 1) : d371795 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d371804 q = 1) : d371804 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d371866 q = 1) : d371866 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d371953 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39245 q selected
    | true =>
      simp only [d371953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39246 q selected
  have h4 (q : Pattern) (selected : d371954 q = 1) : d375422 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371954, d375422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371954, d375422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371960 q = 1) : d371960 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d371961 q = 1) : d375423 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371961, d375423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371961, d375423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371962 q = 1) : d375424 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371962, d375424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371962, d375424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d371963 q = 1) : d375425 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d371963, d375425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371963, d375425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d371970 q = 1) : d371970 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d371975 q = 1) : d371975 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d371977 q = 1) : d371977 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d371980 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39248 q selected
    | true =>
      simp only [d371980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39249 q selected
  have h13 (q : Pattern) (selected : d371981 q = 1) : d375427 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371981, d375427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d371981, d375427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d371984 q = 1) : d371984 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d371985 q = 1) : d375428 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371985, d375428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d371985, d375428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d371986 q = 1) : d375429 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371986, d375429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d371986, d375429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d371987 q = 1) : d375430 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d371987, d375430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371987, d375430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d371988 q = 1) : d375431 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d371988, d375431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d371988, d375431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro39251 (p : Pattern) (selected : d372008 p = 1) : d375438 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d371977 q = 1) : d371977 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d371980 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39248 q selected
    | true =>
      simp only [d371980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39249 q selected
  have h3 (q : Pattern) (selected : d371981 q = 1) : d375427 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371981, d375427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371981, d375427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371984 q = 1) : d371984 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d371985 q = 1) : d375428 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371985, d375428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371985, d375428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372006 q = 1) : d375436 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d372006, d375436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372006, d375436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d372007 q = 1) : d375437 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d372007, d375437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372007, d375437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372008 q = 1) : d375438 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d372008, d375438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372008, d375438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39252 (p : Pattern) (selected : d372118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372100 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39235 q selected
  have h2 (q : Pattern) (selected : d371884 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39235 q selected
    | true =>
      simp only [d371884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d372101 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371885 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372102 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372103 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372104 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39236 q selected
  have h8 (q : Pattern) (selected : d371896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39236 q selected
    | true =>
      simp only [d371896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d372105 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371897 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d371897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d372106 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d372107 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d372107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d372108 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d372109 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39237 q selected
  have h15 (q : Pattern) (selected : d371906 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39237 q selected
    | true =>
      simp only [d371906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d372110 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d372110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d371907 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d371907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d372111 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d372111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d372112 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d372112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d372113 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39238 q selected
  have h21 (q : Pattern) (selected : d371914 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39238 q selected
    | true =>
      simp only [d371914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d372114 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d372114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d371915 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d371915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d372115 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d372115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d372116 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d372116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d372117 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d372117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d372118 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d372118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d372118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro39253 (p : Pattern) (selected : d372125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372119 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39240 q selected
  have h2 (q : Pattern) (selected : d371921 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39240 q selected
    | true =>
      simp only [d371921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d372120 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371922 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372121 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372122 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372113 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39238 q selected
  have h8 (q : Pattern) (selected : d371914 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39238 q selected
    | true =>
      simp only [d371914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d372114 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371915 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d371915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d372115 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d372116 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d372116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d372123 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d372124 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d372124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d372125 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d372125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d372125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro39254 (p : Pattern) (selected : d372129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372113 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39238 q selected
  have h2 (q : Pattern) (selected : d371914 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39238 q selected
    | true =>
      simp only [d371914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d372114 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371915 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372115 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372116 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372124 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d372129 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d372129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39255 (p : Pattern) (selected : d372136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372126 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d372126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39252 q selected
    | true =>
      simp only [d372126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39253 q selected
  have h2 (q : Pattern) (selected : d372127 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d372127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372128 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d372128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372130 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d372130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39253 q selected
    | true =>
      simp only [d372130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39254 q selected
  have h5 (q : Pattern) (selected : d372131 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d372131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372132 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d372132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d372133 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d372133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372134 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d372134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d372135 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d372135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d372136 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d372136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39256 (p : Pattern) (selected : d372140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372130 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d372130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39253 q selected
    | true =>
      simp only [d372130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39254 q selected
  have h2 (q : Pattern) (selected : d372131 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d372131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372132 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d372132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372134 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d372134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372139 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d372139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372140 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d372140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39257 (p : Pattern) (selected : d372146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372137 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39255 q selected
    | true =>
      simp only [d372137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372138 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39256 q selected
    | true =>
      simp only [d372141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d372142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d372143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d372143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372144 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d372144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372145 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d372145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d372146 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d372146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39258 (p : Pattern) (selected : d372150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39256 q selected
    | true =>
      simp only [d372141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372147 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d372147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d372148 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d372148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372149 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d372149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372150 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d372150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39259 (p : Pattern) (selected : d372162 p = 1) : d375448 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372099 q = 1) : d372099 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d372151 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d372151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39257 q selected
    | true =>
      simp only [d372151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39258 q selected
  have h3 (q : Pattern) (selected : d372152 q = 1) : d375444 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d372152, d375444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372152, d375444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372158 q = 1) : d372158 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d372159 q = 1) : d375445 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372159, d375445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372159, d375445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372160 q = 1) : d375446 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d372160, d375446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372160, d375446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d372161 q = 1) : d375447 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d372161, d375447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372161, d375447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372162 q = 1) : d375448 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d372162, d375448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372162, d375448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39260 (p : Pattern) (selected : d372179 p = 1) : d375454 p = 1 := by
  have h0 (q : Pattern) (selected : d371787 q = 1) : d371787 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d371989 q = 1) : d375432 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d371989, d375432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39247 q selected
    | true =>
      simp only [d371989, d375432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39250 q selected
  have h2 (q : Pattern) (selected : d372002 q = 1) : d372002 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d372003 q = 1) : d375433 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d372003, d375433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372003, d375433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d372004 q = 1) : d375434 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d372004, d375434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372004, d375434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372005 q = 1) : d375435 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d372005, d375435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372005, d375435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d372009 q = 1) : d375439 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d372009, d375439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372009, d375439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39251 q selected
  have h8 (q : Pattern) (selected : d372011 q = 1) : d372011 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d372012 q = 1) : d375440 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d372012, d375440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372012, d375440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d372013 q = 1) : d375441 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d372013, d375441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372013, d375441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d372014 q = 1) : d375442 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d372014, d375442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d372014, d375442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d372015 q = 1) : d375443 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d372015, d375443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372015, d375443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d372163 q = 1) : d375449 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d372163, d375449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372163, d375449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39259 q selected
  have h14 (q : Pattern) (selected : d372174 q = 1) : d372174 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d372175 q = 1) : d375450 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d372175, d375450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d372175, d375450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d372176 q = 1) : d375451 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d372176, d375451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d372176, d375451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d372177 q = 1) : d375452 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d372177, d375452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d372177, d375452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d372178 q = 1) : d375453 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d372178, d375453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d372178, d375453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d372179 q = 1) : d375454 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d372179, d375454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d372179, d375454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro39261 (p : Pattern) (selected : d372185 p = 1) : d375460 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372180 q = 1) : d375455 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d372180, d375455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372180, d375455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39260 q selected
  have h2 (q : Pattern) (selected : d372181 q = 1) : d375456 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d372181, d375456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372181, d375456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372182 q = 1) : d375457 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d372182, d375457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372182, d375457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372183 q = 1) : d375458 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d372183, d375458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372183, d375458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d372184 q = 1) : d375459 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d372184, d375459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372184, d375459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372185 q = 1) : d375460 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d372185, d375460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372185, d375460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39262 (p : Pattern) (selected : d372361 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (selected : d339816 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d339816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339821 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d339821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d339821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372361 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d372361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro39263 (p : Pattern) (selected : d372370 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (selected : d339469 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d339469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371532 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d371532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d339816 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d339816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d339821 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d339821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d339821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372370 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d372370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro39264 (p : Pattern) (selected : d372377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372362 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d372362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39262 q selected
  have h2 (q : Pattern) (selected : d372363 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d372363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d372364 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d372364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372365 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d372365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39262 q selected
    | true =>
      simp only [d372365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372366 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d372366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372367 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d372367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d372368 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d372368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372369 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d372369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d372371 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d372371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39263 q selected
    | true =>
      simp only [d372371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35720 q selected
  have h10 (q : Pattern) (selected : d372372 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d372372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d372373 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d372373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d339823 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d339823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35720 q selected
    | true =>
      simp only [d339823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d339824 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d339824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d339824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d372374 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d372374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d372375 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d372375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d372375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d372376 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d372376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d372376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d372377 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d372377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d372377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro39265 (p : Pattern) (selected : d372387 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (selected : d339469 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d339469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371532 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d371532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372387 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d372387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39266 (p : Pattern) (selected : d372393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372362 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d372362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39262 q selected
  have h2 (q : Pattern) (selected : d372363 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d372363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d372371 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d372371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39263 q selected
    | true =>
      simp only [d372371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35720 q selected
  have h4 (q : Pattern) (selected : d372372 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d372372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372373 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d372373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372382 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d372382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39263 q selected
    | true =>
      simp only [d372382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372383 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d372383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d339823 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d339823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35720 q selected
    | true =>
      simp only [d339823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d339824 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d339824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d339824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d372384 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d372384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d372385 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d372385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d372386 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d372386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d372386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d372388 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d372388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39265 q selected
    | true =>
      simp only [d372388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35779 q selected
  have h14 (q : Pattern) (selected : d340699 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d340699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d340699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35666 q selected
  have h15 (q : Pattern) (selected : d372389 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d372389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d372389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d372390 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d372390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d372390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h17 (q : Pattern) (selected : d372391 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d372391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d372391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d372392 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d372392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d372392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d372393 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d372393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d372393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro39267 (p : Pattern) (selected : d372404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372362 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d372362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39262 q selected
  have h2 (q : Pattern) (selected : d372363 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d372363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d372399 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d372399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39265 q selected
    | true =>
      simp only [d372399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d372400 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d372400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372401 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d372401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372402 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d372402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372403 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d372403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d372388 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d372388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39265 q selected
    | true =>
      simp only [d372388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35779 q selected
  have h9 (q : Pattern) (selected : d340699 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d340699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d340699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35666 q selected
  have h10 (q : Pattern) (selected : d372389 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d372389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d372389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d339823 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d339823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35720 q selected
    | true =>
      simp only [d339823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d339824 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d339824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d339824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d372390 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d372390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d372390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d372391 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d372391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d372391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d372392 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d372392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d372392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d372404 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d372404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro39268 (p : Pattern) (selected : d372414 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d372409 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d372409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39263 q selected
    | true =>
      simp only [d372409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35779 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d340699 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d340699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d340699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35666 q selected
  have h3 (q : Pattern) (selected : d372410 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d372410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d339823 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d339823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35720 q selected
    | true =>
      simp only [d339823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d339824 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d339824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d339824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d372411 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d372411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d340280 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d340280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d340280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d372412 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d372412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d372413 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d372413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d372413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d372414 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d372414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h10 p selected
theorem eqIntro39269 (p : Pattern) (selected : d372420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372378 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39264 q selected
    | true =>
      simp only [d372378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372379 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d372380 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372394 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39266 q selected
    | true =>
      simp only [d372394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372395 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372396 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372397 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d372398 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d372405 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39267 q selected
    | true =>
      simp only [d372405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d372406 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d372406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d372407 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d372408 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d372408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d372415 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39268 q selected
    | true =>
      simp only [d372415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d372416 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d372416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d372417 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d372418 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d372418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d372419 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d372419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d372420 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d372420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro39270 (p : Pattern) (selected : d372421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372362 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d372362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39262 q selected
  have h2 (q : Pattern) (selected : d372363 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d372363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d372371 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d372371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39263 q selected
    | true =>
      simp only [d372371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35720 q selected
  have h4 (q : Pattern) (selected : d372372 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d372372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372373 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d372373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372382 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d372382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39263 q selected
    | true =>
      simp only [d372382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372383 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d372383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d339823 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d339823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35720 q selected
    | true =>
      simp only [d339823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d339824 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d339824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d339824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d372384 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d372384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d372385 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d372385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d372386 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d372386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d372386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d372409 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d372409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39263 q selected
    | true =>
      simp only [d372409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35779 q selected
  have h14 (q : Pattern) (selected : d340699 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d340699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d340699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35666 q selected
  have h15 (q : Pattern) (selected : d372410 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d372410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d372410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d372411 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d372411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d372411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h17 (q : Pattern) (selected : d340280 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d340280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d340280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d372412 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d372412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d372412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d372413 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d372413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d372413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d372421 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d372421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d372421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  exact h20 p selected
theorem eqIntro39271 (p : Pattern) (selected : d372428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372422 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39270 q selected
    | true =>
      simp only [d372422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372423 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d372424 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372425 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372415 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39268 q selected
    | true =>
      simp only [d372415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372416 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372417 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372418 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d372426 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d372427 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d372427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d372428 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d372428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39272 (p : Pattern) (selected : d372432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372415 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39268 q selected
    | true =>
      simp only [d372415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372416 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d372417 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372418 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372427 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372432 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d372432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39273 (p : Pattern) (selected : d372439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372429 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d372429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39269 q selected
    | true =>
      simp only [d372429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39271 q selected
  have h2 (q : Pattern) (selected : d372430 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d372430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372431 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d372431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372433 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d372433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39271 q selected
    | true =>
      simp only [d372433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39272 q selected
  have h5 (q : Pattern) (selected : d372434 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d372434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372435 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d372435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d372436 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d372436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372437 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d372437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d372438 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d372438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d372439 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d372439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39274 (p : Pattern) (selected : d372443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372433 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d372433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39271 q selected
    | true =>
      simp only [d372433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39272 q selected
  have h2 (q : Pattern) (selected : d372434 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d372434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372435 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d372435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372437 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d372437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372442 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d372442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372443 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d372443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39275 (p : Pattern) (selected : d372449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372440 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39273 q selected
    | true =>
      simp only [d372440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372441 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372444 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39274 q selected
    | true =>
      simp only [d372444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d372445 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d372446 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d372446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372447 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d372447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372448 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d372448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d372449 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d372449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39276 (p : Pattern) (selected : d372453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372444 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39274 q selected
    | true =>
      simp only [d372444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372445 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372450 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d372450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d372451 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d372451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372452 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d372452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372453 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d372453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39277 (p : Pattern) (selected : d372465 p = 1) : d375468 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372305 q = 1) : d372305 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d372314 q = 1) : d372314 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d372360 q = 1) : d372360 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d372454 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d372454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39275 q selected
    | true =>
      simp only [d372454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39276 q selected
  have h5 (q : Pattern) (selected : d372455 q = 1) : d375464 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d372455, d375464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372455, d375464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372461 q = 1) : d372461 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d372462 q = 1) : d375465 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372462, d375465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372462, d375465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372463 q = 1) : d375466 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d372463, d375466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372463, d375466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d372464 q = 1) : d375467 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d372464, d375467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372464, d375467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d372465 q = 1) : d375468 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d372465, d375468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372465, d375468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro39278 (p : Pattern) (selected : d372479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372440 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39273 q selected
    | true =>
      simp only [d372440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372441 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372444 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39274 q selected
    | true =>
      simp only [d372444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d372445 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d372446 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d372446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372447 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d372447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372448 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d372448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d372479 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d372479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39279 (p : Pattern) (selected : d372480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372444 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39274 q selected
    | true =>
      simp only [d372444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372445 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372450 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d372450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d372451 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d372451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372452 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d372452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372480 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d372480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39280 (p : Pattern) (selected : d372489 p = 1) : d375473 p = 1 := by
  have h0 (q : Pattern) (selected : d372305 q = 1) : d372305 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372314 q = 1) : d372314 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d372360 q = 1) : d372360 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d372454 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d372454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39275 q selected
    | true =>
      simp only [d372454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39276 q selected
  have h4 (q : Pattern) (selected : d372455 q = 1) : d375464 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d372455, d375464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372455, d375464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d372461 q = 1) : d372461 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d372462 q = 1) : d375465 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372462, d375465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372462, d375465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d372463 q = 1) : d375466 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d372463, d375466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372463, d375466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372464 q = 1) : d375467 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d372464, d375467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372464, d375467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d372471 q = 1) : d372471 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d372476 q = 1) : d372476 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d372478 q = 1) : d372478 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d372481 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d372481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39278 q selected
    | true =>
      simp only [d372481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39279 q selected
  have h13 (q : Pattern) (selected : d372482 q = 1) : d375469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d372482, d375469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d372482, d375469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d372485 q = 1) : d372485 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d372486 q = 1) : d375470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372486, d375470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d372486, d375470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d372487 q = 1) : d375471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d372487, d375471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d372487, d375471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d372488 q = 1) : d375472 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d372488, d375472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372488, d375472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d372489 q = 1) : d375473 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d372489, d375473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d372489, d375473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro39281 (p : Pattern) (selected : d372509 p = 1) : d375480 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372478 q = 1) : d372478 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d372481 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d372481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39278 q selected
    | true =>
      simp only [d372481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39279 q selected
  have h3 (q : Pattern) (selected : d372482 q = 1) : d375469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d372482, d375469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372482, d375469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372485 q = 1) : d372485 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d372486 q = 1) : d375470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372486, d375470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372486, d375470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372507 q = 1) : d375478 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d372507, d375478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372507, d375478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d372508 q = 1) : d375479 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d372508, d375479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372508, d375479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372509 q = 1) : d375480 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d372509, d375480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372509, d375480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39282 (p : Pattern) (selected : d372619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372601 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39264 q selected
  have h2 (q : Pattern) (selected : d372378 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39264 q selected
    | true =>
      simp only [d372378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d372602 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372379 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372603 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372604 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372605 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39266 q selected
  have h8 (q : Pattern) (selected : d372394 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39266 q selected
    | true =>
      simp only [d372394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d372606 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d372395 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d372395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d372607 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d372608 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d372608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d372609 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d372610 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39267 q selected
  have h15 (q : Pattern) (selected : d372405 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39267 q selected
    | true =>
      simp only [d372405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d372611 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d372611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d372406 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d372406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d372612 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d372612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d372613 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d372613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d372614 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39268 q selected
  have h21 (q : Pattern) (selected : d372415 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39268 q selected
    | true =>
      simp only [d372415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d372615 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d372615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d372416 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d372416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d372616 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d372616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d372617 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d372617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d372618 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d372618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d372619 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d372619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d372619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro39283 (p : Pattern) (selected : d372626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372620 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39270 q selected
  have h2 (q : Pattern) (selected : d372422 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39270 q selected
    | true =>
      simp only [d372422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d372621 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372423 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372622 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372623 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372614 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39268 q selected
  have h8 (q : Pattern) (selected : d372415 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39268 q selected
    | true =>
      simp only [d372415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d372615 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d372416 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d372416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d372616 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d372617 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d372617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d372624 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d372625 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d372625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d372626 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d372626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d372626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro39284 (p : Pattern) (selected : d372630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372614 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39268 q selected
  have h2 (q : Pattern) (selected : d372415 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39268 q selected
    | true =>
      simp only [d372415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d372615 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372416 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372616 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372617 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372625 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d372630 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d372630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39285 (p : Pattern) (selected : d372637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372627 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d372627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39282 q selected
    | true =>
      simp only [d372627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39283 q selected
  have h2 (q : Pattern) (selected : d372628 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d372628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372629 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d372629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372631 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d372631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39283 q selected
    | true =>
      simp only [d372631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39284 q selected
  have h5 (q : Pattern) (selected : d372632 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d372632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372633 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d372633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d372634 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d372634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372635 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d372635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d372636 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d372636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d372637 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d372637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39286 (p : Pattern) (selected : d372641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372631 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d372631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39283 q selected
    | true =>
      simp only [d372631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39284 q selected
  have h2 (q : Pattern) (selected : d372632 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d372632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372633 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d372633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372635 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d372635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372640 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d372640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372641 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d372641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39287 (p : Pattern) (selected : d372647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372638 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39285 q selected
    | true =>
      simp only [d372638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372639 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372642 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39286 q selected
    | true =>
      simp only [d372642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d372643 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d372644 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d372644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372645 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d372645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372646 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d372646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d372647 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d372647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39288 (p : Pattern) (selected : d372651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372642 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39286 q selected
    | true =>
      simp only [d372642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372643 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d372648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d372649 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d372649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372650 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d372650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372651 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d372651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39289 (p : Pattern) (selected : d372663 p = 1) : d375490 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372600 q = 1) : d372600 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d372652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d372652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39287 q selected
    | true =>
      simp only [d372652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39288 q selected
  have h3 (q : Pattern) (selected : d372653 q = 1) : d375486 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d372653, d375486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372653, d375486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372659 q = 1) : d372659 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d372660 q = 1) : d375487 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372660, d375487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372660, d375487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372661 q = 1) : d375488 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d372661, d375488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372661, d375488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d372662 q = 1) : d375489 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d372662, d375489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372662, d375489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372663 q = 1) : d375490 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d372663, d375490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372663, d375490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39290 (p : Pattern) (selected : d372680 p = 1) : d375496 p = 1 := by
  have h0 (q : Pattern) (selected : d372297 q = 1) : d372297 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372490 q = 1) : d375474 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d372490, d375474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39277 q selected
    | true =>
      simp only [d372490, d375474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39280 q selected
  have h2 (q : Pattern) (selected : d372503 q = 1) : d372503 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d372504 q = 1) : d375475 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d372504, d375475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372504, d375475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d372505 q = 1) : d375476 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d372505, d375476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372505, d375476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372506 q = 1) : d375477 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d372506, d375477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372506, d375477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d372510 q = 1) : d375481 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d372510, d375481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372510, d375481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39281 q selected
  have h8 (q : Pattern) (selected : d372512 q = 1) : d372512 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d372513 q = 1) : d375482 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d372513, d375482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372513, d375482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d372514 q = 1) : d375483 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d372514, d375483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372514, d375483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d372515 q = 1) : d375484 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d372515, d375484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d372515, d375484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d372516 q = 1) : d375485 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d372516, d375485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372516, d375485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d372664 q = 1) : d375491 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d372664, d375491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372664, d375491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39289 q selected
  have h14 (q : Pattern) (selected : d372675 q = 1) : d372675 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d372676 q = 1) : d375492 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d372676, d375492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d372676, d375492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d372677 q = 1) : d375493 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d372677, d375493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d372677, d375493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d372678 q = 1) : d375494 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d372678, d375494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d372678, d375494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d372679 q = 1) : d375495 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d372679, d375495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d372679, d375495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d372680 q = 1) : d375496 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d372680, d375496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d372680, d375496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro39291 (p : Pattern) (selected : d372686 p = 1) : d375502 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372681 q = 1) : d375497 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d372681, d375497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372681, d375497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39290 q selected
  have h2 (q : Pattern) (selected : d372682 q = 1) : d375498 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d372682, d375498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372682, d375498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372683 q = 1) : d375499 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d372683, d375499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372683, d375499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372684 q = 1) : d375500 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d372684, d375500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372684, d375500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d372685 q = 1) : d375501 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d372685, d375501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372685, d375501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372686 q = 1) : d375502 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d372686, d375502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372686, d375502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39292 (p : Pattern) (selected : d372792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372786 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d372786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39265 q selected
  have h2 (q : Pattern) (selected : d372787 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d372787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35720 q selected
  have h3 (q : Pattern) (selected : d372788 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d372788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372789 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d372789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372790 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d372790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372791 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d372791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372792 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d372792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro39293 (p : Pattern) (selected : d372798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372786 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d372786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39265 q selected
  have h2 (q : Pattern) (selected : d372787 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d372787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35720 q selected
  have h3 (q : Pattern) (selected : d372788 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d372788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372789 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d372789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372790 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d372790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372791 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d372791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372798 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d372798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro39294 (p : Pattern) (selected : d372804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372793 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39292 q selected
    | true =>
      simp only [d372793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372794 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d372795 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372796 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372797 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372799 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39293 q selected
    | true =>
      simp only [d372799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372800 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d372801 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d372802 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d372802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d372803 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d372804 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d372804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39295 (p : Pattern) (selected : d372806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372793 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39292 q selected
    | true =>
      simp only [d372793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372794 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d372795 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372796 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372799 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39293 q selected
    | true =>
      simp only [d372799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372800 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372801 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372802 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d372803 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d372805 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d372805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d372806 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d372806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39296 (p : Pattern) (selected : d372810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372799 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39293 q selected
    | true =>
      simp only [d372799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372800 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d372801 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372802 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372805 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372810 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d372810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39297 (p : Pattern) (selected : d372817 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372807 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d372807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39294 q selected
    | true =>
      simp only [d372807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39295 q selected
  have h2 (q : Pattern) (selected : d372808 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d372808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372809 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d372809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372811 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d372811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39295 q selected
    | true =>
      simp only [d372811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39296 q selected
  have h5 (q : Pattern) (selected : d372812 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d372812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372813 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d372813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d372814 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d372814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372815 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d372815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d372816 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d372816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d372817 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d372817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39298 (p : Pattern) (selected : d372821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372811 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d372811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39295 q selected
    | true =>
      simp only [d372811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39296 q selected
  have h2 (q : Pattern) (selected : d372812 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d372812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372813 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d372813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372815 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d372815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372820 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d372820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372821 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d372821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39299 (p : Pattern) (selected : d372827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372818 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39297 q selected
    | true =>
      simp only [d372818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372819 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372822 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39298 q selected
    | true =>
      simp only [d372822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d372823 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d372824 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d372824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372825 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d372825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372826 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d372826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d372827 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d372827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39300 (p : Pattern) (selected : d372831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372822 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39298 q selected
    | true =>
      simp only [d372822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372823 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372828 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d372828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d372829 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d372829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372830 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d372830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372831 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d372831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39301 (p : Pattern) (selected : d372843 p = 1) : d375511 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372762 q = 1) : d372762 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d372771 q = 1) : d372771 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d372785 q = 1) : d372785 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d372832 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d372832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39299 q selected
    | true =>
      simp only [d372832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39300 q selected
  have h5 (q : Pattern) (selected : d372833 q = 1) : d375507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d372833, d375507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372833, d375507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372839 q = 1) : d372839 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d372840 q = 1) : d375508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372840, d375508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372840, d375508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372841 q = 1) : d375509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d372841, d375509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372841, d375509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d372842 q = 1) : d375510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d372842, d375510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372842, d375510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d372843 q = 1) : d375511 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d372843, d375511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372843, d375511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro39302 (p : Pattern) (selected : d372857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372818 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39297 q selected
    | true =>
      simp only [d372818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372819 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372822 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39298 q selected
    | true =>
      simp only [d372822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d372823 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d372824 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d372824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372825 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d372825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372826 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d372826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d372857 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d372857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39303 (p : Pattern) (selected : d372858 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372822 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39298 q selected
    | true =>
      simp only [d372822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372823 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372828 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d372828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d372829 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d372829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372830 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d372830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372858 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d372858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39304 (p : Pattern) (selected : d372867 p = 1) : d375516 p = 1 := by
  have h0 (q : Pattern) (selected : d372762 q = 1) : d372762 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372771 q = 1) : d372771 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d372785 q = 1) : d372785 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d372832 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d372832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39299 q selected
    | true =>
      simp only [d372832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39300 q selected
  have h4 (q : Pattern) (selected : d372833 q = 1) : d375507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d372833, d375507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372833, d375507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d372839 q = 1) : d372839 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d372840 q = 1) : d375508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372840, d375508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372840, d375508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d372841 q = 1) : d375509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d372841, d375509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372841, d375509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372842 q = 1) : d375510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d372842, d375510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372842, d375510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d372849 q = 1) : d372849 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d372854 q = 1) : d372854 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d372856 q = 1) : d372856 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d372859 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d372859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39302 q selected
    | true =>
      simp only [d372859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39303 q selected
  have h13 (q : Pattern) (selected : d372860 q = 1) : d375512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d372860, d375512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d372860, d375512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d372863 q = 1) : d372863 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d372864 q = 1) : d375513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372864, d375513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d372864, d375513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d372865 q = 1) : d375514 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d372865, d375514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d372865, d375514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d372866 q = 1) : d375515 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d372866, d375515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372866, d375515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d372867 q = 1) : d375516 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d372867, d375516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d372867, d375516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro39305 (p : Pattern) (selected : d372887 p = 1) : d375523 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372856 q = 1) : d372856 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d372859 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d372859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39302 q selected
    | true =>
      simp only [d372859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39303 q selected
  have h3 (q : Pattern) (selected : d372860 q = 1) : d375512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d372860, d375512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372860, d375512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372863 q = 1) : d372863 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d372864 q = 1) : d375513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372864, d375513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372864, d375513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372885 q = 1) : d375521 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d372885, d375521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372885, d375521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d372886 q = 1) : d375522 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d372886, d375522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372886, d375522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372887 q = 1) : d375523 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d372887, d375523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372887, d375523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39306 (p : Pattern) (selected : d372953 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372943 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39292 q selected
  have h2 (q : Pattern) (selected : d372793 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39292 q selected
    | true =>
      simp only [d372793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d372944 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372794 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372945 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372946 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372947 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372948 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39293 q selected
  have h9 (q : Pattern) (selected : d372799 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39293 q selected
    | true =>
      simp only [d372799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d372949 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d372949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d372800 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d372950 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d372950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d372951 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d372951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d372952 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d372953 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d372953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro39307 (p : Pattern) (selected : d372955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372943 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39292 q selected
  have h2 (q : Pattern) (selected : d372793 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39292 q selected
    | true =>
      simp only [d372793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d372944 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372794 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372945 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372946 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372948 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39293 q selected
  have h8 (q : Pattern) (selected : d372799 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39293 q selected
    | true =>
      simp only [d372799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d372949 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d372800 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d372800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d372950 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d372951 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d372951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d372952 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d372954 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d372954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d372955 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d372955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d372955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro39308 (p : Pattern) (selected : d372959 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372948 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39293 q selected
  have h2 (q : Pattern) (selected : d372799 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d372799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39293 q selected
    | true =>
      simp only [d372799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d372949 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372800 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d372800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372950 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d372950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372951 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d372951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372954 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d372954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d372959 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d372959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39309 (p : Pattern) (selected : d372966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372956 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d372956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39306 q selected
    | true =>
      simp only [d372956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39307 q selected
  have h2 (q : Pattern) (selected : d372957 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d372957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372958 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d372958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372960 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d372960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39307 q selected
    | true =>
      simp only [d372960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39308 q selected
  have h5 (q : Pattern) (selected : d372961 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d372961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372962 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d372962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d372963 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d372963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372964 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d372964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d372965 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d372965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d372966 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d372966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39310 (p : Pattern) (selected : d372970 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372960 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d372960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39307 q selected
    | true =>
      simp only [d372960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39308 q selected
  have h2 (q : Pattern) (selected : d372961 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d372961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372962 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d372962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372964 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d372964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372969 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d372969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372970 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d372970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39311 (p : Pattern) (selected : d372976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39309 q selected
    | true =>
      simp only [d372967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372971 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39310 q selected
    | true =>
      simp only [d372971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d372972 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d372973 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d372973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372974 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d372974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d372975 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d372975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d372976 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d372976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39312 (p : Pattern) (selected : d372980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372971 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d372971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39310 q selected
    | true =>
      simp only [d372971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d372972 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d372972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d372977 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d372977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d372977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d372978 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d372978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d372979 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d372979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d372980 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d372980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d372980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39313 (p : Pattern) (selected : d372992 p = 1) : d375533 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372942 q = 1) : d372942 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d372981 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d372981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39311 q selected
    | true =>
      simp only [d372981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39312 q selected
  have h3 (q : Pattern) (selected : d372982 q = 1) : d375529 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d372982, d375529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372982, d375529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372988 q = 1) : d372988 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d372989 q = 1) : d375530 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372989, d375530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372989, d375530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372990 q = 1) : d375531 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d372990, d375531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372990, d375531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d372991 q = 1) : d375532 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d372991, d375532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372991, d375532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d372992 q = 1) : d375533 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d372992, d375533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372992, d375533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39314 (p : Pattern) (selected : d373009 p = 1) : d375539 p = 1 := by
  have h0 (q : Pattern) (selected : d372754 q = 1) : d372754 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d372868 q = 1) : d375517 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d372868, d375517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39301 q selected
    | true =>
      simp only [d372868, d375517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39304 q selected
  have h2 (q : Pattern) (selected : d372881 q = 1) : d372881 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d372882 q = 1) : d375518 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d372882, d375518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372882, d375518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d372883 q = 1) : d375519 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d372883, d375519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372883, d375519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372884 q = 1) : d375520 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d372884, d375520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d372884, d375520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d372888 q = 1) : d375524 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d372888, d375524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372888, d375524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39305 q selected
  have h8 (q : Pattern) (selected : d372890 q = 1) : d372890 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d372891 q = 1) : d375525 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d372891, d375525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d372891, d375525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d372892 q = 1) : d375526 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d372892, d375526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d372892, d375526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d372893 q = 1) : d375527 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d372893, d375527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d372893, d375527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d372894 q = 1) : d375528 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d372894, d375528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372894, d375528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d372993 q = 1) : d375534 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d372993, d375534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372993, d375534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39313 q selected
  have h14 (q : Pattern) (selected : d373004 q = 1) : d373004 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d373005 q = 1) : d375535 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373005, d375535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d373005, d375535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d373006 q = 1) : d375536 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d373006, d375536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d373006, d375536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d373007 q = 1) : d375537 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d373007, d375537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d373007, d375537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d373008 q = 1) : d375538 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d373008, d375538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d373008, d375538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d373009 q = 1) : d375539 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d373009, d375539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d373009, d375539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro39315 (p : Pattern) (selected : d373015 p = 1) : d375545 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d373010 q = 1) : d375540 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d373010, d375540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d373010, d375540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39314 q selected
  have h2 (q : Pattern) (selected : d373011 q = 1) : d375541 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d373011, d375541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d373011, d375541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d373012 q = 1) : d375542 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d373012, d375542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d373012, d375542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d373013 q = 1) : d375543 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d373013, d375543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d373013, d375543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d373014 q = 1) : d375544 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d373014, d375544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d373014, d375544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d373015 q = 1) : d375545 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d373015, d375545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d373015, d375545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39316 (p : Pattern) (selected : d373021 p = 1) : d375551 p = 1 := by
  have h0 (q : Pattern) (selected : d371442 q = 1) : d375380 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d371442, d375380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35680 q selected
    | true =>
      simp only [d371442, d375380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39217 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d371687 q = 1) : d375420 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d371687, d375420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371687, d375420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39232 q selected
  have h3 (q : Pattern) (selected : d371688 q = 1) : d375421 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d371688, d375421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371688, d375421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d372186 q = 1) : d375461 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d372186, d375461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372186, d375461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39261 q selected
  have h5 (q : Pattern) (selected : d372187 q = 1) : d375462 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d372187, d375462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372187, d375462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d372188 q = 1) : d375463 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d372188, d375463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372188, d375463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d372687 q = 1) : d375503 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d372687, d375503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372687, d375503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39291 q selected
  have h8 (q : Pattern) (selected : d372688 q = 1) : d375504 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d372688, d375504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372688, d375504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d372689 q = 1) : d375505 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d372689, d375505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d372689, d375505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d372690 q = 1) : d375506 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d372690, d375506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372690, d375506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d373016 q = 1) : d375546 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d373016, d375546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d373016, d375546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39315 q selected
  have h12 (q : Pattern) (selected : d373017 q = 1) : d375547 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d373017, d375547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d373017, d375547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d373018 q = 1) : d375548 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d373018, d375548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d373018, d375548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d373019 q = 1) : d375549 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d373019, d375549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d373019, d375549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d373020 q = 1) : d375550 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d373020, d375550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d373020, d375550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d373021 q = 1) : d375551 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d373021, d375551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d373021, d375551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro39317 (p : Pattern) (selected : d373027 p = 1) : d375557 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d373022 q = 1) : d375552 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d373022, d375552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39316 q selected
    | true =>
      simp only [d373022, d375552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d373023 q = 1) : d375553 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d373023, d375553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d373023, d375553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d373024 q = 1) : d375554 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d373024, d375554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d373024, d375554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d373025 q = 1) : d375555 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d373025, d375555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d373025, d375555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d373026 q = 1) : d375556 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d373026, d375556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d373026, d375556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d373027 q = 1) : d375557 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d373027, d375557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d373027, d375557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39318 (p : Pattern) (selected : d373033 p = 1) : d375563 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d373028 q = 1) : d375558 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d373028, d375558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39317 q selected
    | true =>
      simp only [d373028, d375558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d373029 q = 1) : d375559 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d373029, d375559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d373029, d375559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d373030 q = 1) : d375560 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d373030, d375560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d373030, d375560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d373031 q = 1) : d375561 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d373031, d375561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d373031, d375561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d373032 q = 1) : d375562 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d373032, d375562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d373032, d375562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d373033 q = 1) : d375563 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d373033, d375563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d373033, d375563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39319 (p : Pattern) (selected : d373039 p = 1) : d375569 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d373034 q = 1) : d375564 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d373034, d375564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39318 q selected
    | true =>
      simp only [d373034, d375564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d373035 q = 1) : d375565 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d373035, d375565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d373035, d375565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d373036 q = 1) : d375566 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d373036, d375566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d373036, d375566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d373037 q = 1) : d375567 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d373037, d375567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d373037, d375567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d373038 q = 1) : d375568 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d373038, d375568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d373038, d375568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d373039 q = 1) : d375569 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d373039, d375569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d373039, d375569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39320 (p : Pattern) (selected : d373045 p = 1) : d375575 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d373040 q = 1) : d375570 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d373040, d375570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39319 q selected
    | true =>
      simp only [d373040, d375570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d373041 q = 1) : d375571 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d373041, d375571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d373041, d375571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d373042 q = 1) : d375572 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d373042, d375572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d373042, d375572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d373043 q = 1) : d375573 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d373043, d375573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d373043, d375573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d373044 q = 1) : d375574 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d373044, d375574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d373044, d375574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d373045 q = 1) : d375575 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d373045, d375575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d373045, d375575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39321 (p : Pattern) (selected : d373051 p = 1) : d375581 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d373046 q = 1) : d375576 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d373046, d375576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39320 q selected
    | true =>
      simp only [d373046, d375576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d373047 q = 1) : d375577 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d373047, d375577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d373047, d375577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d373048 q = 1) : d375578 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d373048, d375578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d373048, d375578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d373049 q = 1) : d375579 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d373049, d375579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d373049, d375579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d373050 q = 1) : d375580 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d373050, d375580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d373050, d375580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d373051 q = 1) : d375581 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d373051, d375581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d373051, d375581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39322 (p : Pattern) (selected : d373057 p = 1) : d375587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d373052 q = 1) : d375582 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d373052, d375582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39321 q selected
    | true =>
      simp only [d373052, d375582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d373053 q = 1) : d375583 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d373053, d375583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d373053, d375583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d373054 q = 1) : d375584 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d373054, d375584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d373054, d375584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d373055 q = 1) : d375585 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d373055, d375585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d373055, d375585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d373056 q = 1) : d375586 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d373056, d375586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d373056, d375586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d373057 q = 1) : d375587 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d373057, d375587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d373057, d375587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39323 (p : Pattern) (selected : d373063 p = 1) : d375593 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d373058 q = 1) : d375588 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d373058, d375588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39322 q selected
    | true =>
      simp only [d373058, d375588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d373059 q = 1) : d375589 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d373059, d375589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d373059, d375589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d373060 q = 1) : d375590 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d373060, d375590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d373060, d375590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d373061 q = 1) : d375591 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d373061, d375591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d373061, d375591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d373062 q = 1) : d375592 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d373062, d375592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d373062, d375592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d373063 q = 1) : d375593 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d373063, d375593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d373063, d375593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39324 (p : Pattern) (selected : d47284 p = 0) : d375598 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 0) : d319211 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d319211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33045 q selected
    | true =>
      simp only [d45496, d319211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33107 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d45903 q = 0) : d319500 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45903, d319500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45903, d319500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33184 q selected
  have h3 (q : Pattern) (selected : d45904 q = 0) : d319501 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d45904, d319501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45904, d319501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46456 q = 0) : d319887 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d46456, d319887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46456, d319887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33272 q selected
  have h5 (q : Pattern) (selected : d46457 q = 0) : d319888 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d46457, d319888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46457, d319888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46458 q = 0) : d319889 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d46458, d319889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46458, d319889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46860 q = 0) : d320181 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d46860, d320181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46860, d320181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33351 q selected
  have h8 (q : Pattern) (selected : d46861 q = 0) : d320182 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d46861, d320182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46861, d320182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46862 q = 0) : d320183 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d46862, d320183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46862, d320183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46863 q = 0) : d320184 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d46863, d320184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46863, d320184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47283 q = 0) : d375597 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47283, d375597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47283, d375597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d47284 q = 0) : d375598 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47284, d375598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d47284, d375598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h12 p selected
theorem eqIntro39325 (p : Pattern) (selected : d47290 p = 0) : d375604 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47285 q = 0) : d375599 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47285, d375599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39324 q selected
    | true =>
      simp only [d47285, d375599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47286 q = 0) : d375600 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47286, d375600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47286, d375600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47287 q = 0) : d375601 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47287, d375601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47287, d375601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47288 q = 0) : d375602 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47288, d375602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47288, d375602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47289 q = 0) : d375603 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47289, d375603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47289, d375603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47290 q = 0) : d375604 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47290, d375604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47290, d375604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39326 (p : Pattern) (selected : d47296 p = 0) : d375610 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47291 q = 0) : d375605 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47291, d375605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39325 q selected
    | true =>
      simp only [d47291, d375605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47292 q = 0) : d375606 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47292, d375606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47292, d375606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47293 q = 0) : d375607 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47293, d375607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47293, d375607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47294 q = 0) : d375608 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47294, d375608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47294, d375608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47295 q = 0) : d375609 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47295, d375609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47295, d375609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47296 q = 0) : d375610 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47296, d375610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47296, d375610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39327 (p : Pattern) (selected : d47302 p = 0) : d375616 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47297 q = 0) : d375611 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47297, d375611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39326 q selected
    | true =>
      simp only [d47297, d375611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47298 q = 0) : d375612 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47298, d375612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47298, d375612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47299 q = 0) : d375613 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47299, d375613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47299, d375613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47300 q = 0) : d375614 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47300, d375614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47300, d375614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47301 q = 0) : d375615 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47301, d375615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47301, d375615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47302 q = 0) : d375616 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47302, d375616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47302, d375616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39328 (p : Pattern) (selected : d47308 p = 0) : d375622 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47303 q = 0) : d375617 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47303, d375617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39327 q selected
    | true =>
      simp only [d47303, d375617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47304 q = 0) : d375618 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47304, d375618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47304, d375618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47305 q = 0) : d375619 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47305, d375619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47305, d375619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47306 q = 0) : d375620 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47306, d375620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47306, d375620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47307 q = 0) : d375621 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47307, d375621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47307, d375621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47308 q = 0) : d375622 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47308, d375622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47308, d375622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39329 (p : Pattern) (selected : d47314 p = 0) : d375628 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47309 q = 0) : d375623 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47309, d375623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39328 q selected
    | true =>
      simp only [d47309, d375623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47310 q = 0) : d375624 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47310, d375624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47310, d375624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47311 q = 0) : d375625 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47311, d375625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47311, d375625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47312 q = 0) : d375626 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47312, d375626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47312, d375626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47313 q = 0) : d375627 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47313, d375627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47313, d375627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47314 q = 0) : d375628 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47314, d375628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47314, d375628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39330 (p : Pattern) (selected : d47320 p = 0) : d375634 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47315 q = 0) : d375629 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47315, d375629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39329 q selected
    | true =>
      simp only [d47315, d375629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47316 q = 0) : d375630 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47316, d375630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47316, d375630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47317 q = 0) : d375631 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47317, d375631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47317, d375631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47318 q = 0) : d375632 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47318, d375632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47318, d375632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47319 q = 0) : d375633 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47319, d375633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47319, d375633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47320 q = 0) : d375634 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47320, d375634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47320, d375634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39331 (p : Pattern) (selected : d47326 p = 0) : d375640 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47321 q = 0) : d375635 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47321, d375635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39330 q selected
    | true =>
      simp only [d47321, d375635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47322 q = 0) : d375636 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47322, d375636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47322, d375636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47323 q = 0) : d375637 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47323, d375637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47323, d375637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47324 q = 0) : d375638 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47324, d375638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47324, d375638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47325 q = 0) : d375639 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47325, d375639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47325, d375639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47326 q = 0) : d375640 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47326, d375640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47326, d375640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39332 (p : Pattern) (selected : d47284 p = 1) : d375642 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 1) : d322122 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d322122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33452 q selected
    | true =>
      simp only [d45496, d322122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33473 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d45903 q = 1) : d322162 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45903, d322162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45903, d322162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33501 q selected
  have h3 (q : Pattern) (selected : d45904 q = 1) : d322163 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d45904, d322163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45904, d322163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46456 q = 1) : d322203 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d46456, d322203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46456, d322203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33532 q selected
  have h5 (q : Pattern) (selected : d46457 q = 1) : d322204 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d46457, d322204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46457, d322204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46458 q = 1) : d322205 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d46458, d322205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46458, d322205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46860 q = 1) : d321678 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d46860, d321678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46860, d321678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33559 q selected
  have h8 (q : Pattern) (selected : d46861 q = 1) : d321679 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d46861, d321679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46861, d321679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46862 q = 1) : d321680 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d46862, d321680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46862, d321680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46863 q = 1) : d322206 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d46863, d322206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46863, d322206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47283 q = 1) : d375641 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47283, d375641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47283, d375641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d47284 q = 1) : d375642 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47284, d375642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d47284, d375642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h12 p selected
theorem eqIntro39333 (p : Pattern) (selected : d47290 p = 1) : d375648 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47285 q = 1) : d375643 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47285, d375643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39332 q selected
    | true =>
      simp only [d47285, d375643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47286 q = 1) : d375644 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47286, d375644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47286, d375644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47287 q = 1) : d375645 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47287, d375645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47287, d375645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47288 q = 1) : d375646 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47288, d375646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47288, d375646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47289 q = 1) : d375647 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47289, d375647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47289, d375647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47290 q = 1) : d375648 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47290, d375648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47290, d375648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39334 (p : Pattern) (selected : d47296 p = 1) : d375654 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47291 q = 1) : d375649 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47291, d375649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39333 q selected
    | true =>
      simp only [d47291, d375649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47292 q = 1) : d375650 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47292, d375650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47292, d375650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47293 q = 1) : d375651 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47293, d375651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47293, d375651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47294 q = 1) : d375652 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47294, d375652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47294, d375652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47295 q = 1) : d375653 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47295, d375653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47295, d375653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47296 q = 1) : d375654 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47296, d375654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47296, d375654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39335 (p : Pattern) (selected : d47302 p = 1) : d375660 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47297 q = 1) : d375655 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47297, d375655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39334 q selected
    | true =>
      simp only [d47297, d375655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47298 q = 1) : d375656 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47298, d375656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47298, d375656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47299 q = 1) : d375657 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47299, d375657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47299, d375657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47300 q = 1) : d375658 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47300, d375658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47300, d375658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47301 q = 1) : d375659 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47301, d375659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47301, d375659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47302 q = 1) : d375660 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47302, d375660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47302, d375660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39336 (p : Pattern) (selected : d47308 p = 1) : d375666 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47303 q = 1) : d375661 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47303, d375661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39335 q selected
    | true =>
      simp only [d47303, d375661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47304 q = 1) : d375662 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47304, d375662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47304, d375662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47305 q = 1) : d375663 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47305, d375663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47305, d375663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47306 q = 1) : d375664 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47306, d375664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47306, d375664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47307 q = 1) : d375665 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47307, d375665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47307, d375665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47308 q = 1) : d375666 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47308, d375666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47308, d375666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39337 (p : Pattern) (selected : d47314 p = 1) : d375672 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47309 q = 1) : d375667 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47309, d375667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39336 q selected
    | true =>
      simp only [d47309, d375667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47310 q = 1) : d375668 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47310, d375668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47310, d375668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47311 q = 1) : d375669 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47311, d375669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47311, d375669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47312 q = 1) : d375670 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47312, d375670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47312, d375670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47313 q = 1) : d375671 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47313, d375671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47313, d375671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47314 q = 1) : d375672 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47314, d375672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47314, d375672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39338 (p : Pattern) (selected : d47320 p = 1) : d375678 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47315 q = 1) : d375673 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47315, d375673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39337 q selected
    | true =>
      simp only [d47315, d375673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47316 q = 1) : d375674 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47316, d375674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47316, d375674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47317 q = 1) : d375675 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47317, d375675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47317, d375675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47318 q = 1) : d375676 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47318, d375676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47318, d375676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47319 q = 1) : d375677 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47319, d375677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47319, d375677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47320 q = 1) : d375678 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47320, d375678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47320, d375678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39339 (p : Pattern) (selected : d47326 p = 1) : d375684 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47321 q = 1) : d375679 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47321, d375679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39338 q selected
    | true =>
      simp only [d47321, d375679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47322 q = 1) : d375680 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47322, d375680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47322, d375680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47323 q = 1) : d375681 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47323, d375681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47323, d375681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47324 q = 1) : d375682 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47324, d375682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47324, d375682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47325 q = 1) : d375683 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47325, d375683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47325, d375683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47326 q = 1) : d375684 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47326, d375684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47326, d375684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39340 (p : Pattern) (selected : d375736 p = 0) : d375779 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 0) : d319211 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d319211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33045 q selected
    | true =>
      simp only [d45496, d319211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33107 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d45903 q = 0) : d319500 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45903, d319500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45903, d319500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33184 q selected
  have h3 (q : Pattern) (selected : d45904 q = 0) : d319501 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d45904, d319501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45904, d319501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46456 q = 0) : d319887 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d46456, d319887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46456, d319887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33272 q selected
  have h5 (q : Pattern) (selected : d46457 q = 0) : d319888 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d46457, d319888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46457, d319888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46458 q = 0) : d319889 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d46458, d319889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46458, d319889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d375735 q = 0) : d375778 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d375735, d375778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d375735, d375778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d375736 q = 0) : d375779 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d375736, d375779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d375736, d375779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro39341 (p : Pattern) (selected : d375742 p = 0) : d375785 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d375737 q = 0) : d375780 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d375737, d375780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39340 q selected
    | true =>
      simp only [d375737, d375780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d375738 q = 0) : d375781 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d375738, d375781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d375738, d375781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d375739 q = 0) : d375782 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d375739, d375782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d375739, d375782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d375740 q = 0) : d375783 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d375740, d375783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d375740, d375783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d375741 q = 0) : d375784 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d375741, d375784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d375741, d375784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d375742 q = 0) : d375785 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d375742, d375785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d375742, d375785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39342 (p : Pattern) (selected : d375747 p = 0) : d375790 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d375743 q = 0) : d375786 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d375743, d375786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39341 q selected
    | true =>
      simp only [d375743, d375786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d375744 q = 0) : d375787 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d375744, d375787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d375744, d375787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d375745 q = 0) : d375788 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d375745, d375788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d375745, d375788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d375746 q = 0) : d375789 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d375746, d375789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d375746, d375789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d375747 q = 0) : d375790 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d375747, d375790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d375747, d375790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39343 (p : Pattern) (selected : d375753 p = 0) : d375796 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d375748 q = 0) : d375791 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d375748, d375791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39342 q selected
    | true =>
      simp only [d375748, d375791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d375749 q = 0) : d375792 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d375749, d375792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d375749, d375792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d375750 q = 0) : d375793 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d375750, d375793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d375750, d375793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d375751 q = 0) : d375794 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d375751, d375794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d375751, d375794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d375752 q = 0) : d375795 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d375752, d375795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d375752, d375795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d375753 q = 0) : d375796 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d375753, d375796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d375753, d375796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39344 (p : Pattern) (selected : d375759 p = 0) : d375802 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d375754 q = 0) : d375797 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d375754, d375797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39343 q selected
    | true =>
      simp only [d375754, d375797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d375755 q = 0) : d375798 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d375755, d375798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d375755, d375798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d375756 q = 0) : d375799 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d375756, d375799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d375756, d375799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d375757 q = 0) : d375800 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d375757, d375800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d375757, d375800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d375758 q = 0) : d375801 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d375758, d375801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d375758, d375801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d375759 q = 0) : d375802 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d375759, d375802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d375759, d375802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39345 (p : Pattern) (selected : d375765 p = 0) : d375808 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d375760 q = 0) : d375803 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d375760, d375803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39344 q selected
    | true =>
      simp only [d375760, d375803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d375761 q = 0) : d375804 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d375761, d375804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d375761, d375804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d375762 q = 0) : d375805 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d375762, d375805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d375762, d375805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d375763 q = 0) : d375806 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d375763, d375806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d375763, d375806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d375764 q = 0) : d375807 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d375764, d375807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d375764, d375807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d375765 q = 0) : d375808 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d375765, d375808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d375765, d375808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39346 (p : Pattern) (selected : d375771 p = 0) : d375814 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d375766 q = 0) : d375809 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d375766, d375809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39345 q selected
    | true =>
      simp only [d375766, d375809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d375767 q = 0) : d375810 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d375767, d375810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d375767, d375810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d375768 q = 0) : d375811 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d375768, d375811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d375768, d375811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d375769 q = 0) : d375812 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d375769, d375812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d375769, d375812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d375770 q = 0) : d375813 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d375770, d375813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d375770, d375813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d375771 q = 0) : d375814 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d375771, d375814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d375771, d375814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39347 (p : Pattern) (selected : d375777 p = 0) : d375820 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d375772 q = 0) : d375815 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d375772, d375815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39346 q selected
    | true =>
      simp only [d375772, d375815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d375773 q = 0) : d375816 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d375773, d375816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d375773, d375816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d375774 q = 0) : d375817 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d375774, d375817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d375774, d375817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d375775 q = 0) : d375818 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d375775, d375818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d375775, d375818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d375776 q = 0) : d375819 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d375776, d375819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d375776, d375819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d375777 q = 0) : d375820 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d375777, d375820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d375777, d375820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39348 (p : Pattern) (selected : d375736 p = 1) : d375822 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 1) : d322122 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d322122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33452 q selected
    | true =>
      simp only [d45496, d322122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33473 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d45903 q = 1) : d322162 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45903, d322162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45903, d322162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33501 q selected
  have h3 (q : Pattern) (selected : d45904 q = 1) : d322163 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d45904, d322163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45904, d322163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46456 q = 1) : d322203 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d46456, d322203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46456, d322203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33532 q selected
  have h5 (q : Pattern) (selected : d46457 q = 1) : d322204 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d46457, d322204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46457, d322204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46458 q = 1) : d322205 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d46458, d322205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46458, d322205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d375735 q = 1) : d375821 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d375735, d375821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d375735, d375821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d375736 q = 1) : d375822 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d375736, d375822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d375736, d375822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro39349 (p : Pattern) (selected : d375742 p = 1) : d375828 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d375737 q = 1) : d375823 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d375737, d375823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39348 q selected
    | true =>
      simp only [d375737, d375823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d375738 q = 1) : d375824 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d375738, d375824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d375738, d375824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d375739 q = 1) : d375825 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d375739, d375825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d375739, d375825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d375740 q = 1) : d375826 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d375740, d375826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d375740, d375826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d375741 q = 1) : d375827 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d375741, d375827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d375741, d375827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d375742 q = 1) : d375828 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d375742, d375828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d375742, d375828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39350 (p : Pattern) (selected : d375747 p = 1) : d375833 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d375743 q = 1) : d375829 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d375743, d375829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39349 q selected
    | true =>
      simp only [d375743, d375829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d375744 q = 1) : d375830 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d375744, d375830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d375744, d375830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d375745 q = 1) : d375831 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d375745, d375831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d375745, d375831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d375746 q = 1) : d375832 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d375746, d375832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d375746, d375832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d375747 q = 1) : d375833 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d375747, d375833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d375747, d375833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39351 (p : Pattern) (selected : d375753 p = 1) : d375839 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d375748 q = 1) : d375834 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d375748, d375834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39350 q selected
    | true =>
      simp only [d375748, d375834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d375749 q = 1) : d375835 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d375749, d375835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d375749, d375835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d375750 q = 1) : d375836 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d375750, d375836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d375750, d375836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d375751 q = 1) : d375837 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d375751, d375837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d375751, d375837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d375752 q = 1) : d375838 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d375752, d375838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d375752, d375838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d375753 q = 1) : d375839 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d375753, d375839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d375753, d375839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39352 (p : Pattern) (selected : d375759 p = 1) : d375845 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d375754 q = 1) : d375840 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d375754, d375840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39351 q selected
    | true =>
      simp only [d375754, d375840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d375755 q = 1) : d375841 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d375755, d375841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d375755, d375841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d375756 q = 1) : d375842 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d375756, d375842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d375756, d375842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d375757 q = 1) : d375843 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d375757, d375843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d375757, d375843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d375758 q = 1) : d375844 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d375758, d375844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d375758, d375844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d375759 q = 1) : d375845 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d375759, d375845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d375759, d375845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39353 (p : Pattern) (selected : d375765 p = 1) : d375851 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d375760 q = 1) : d375846 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d375760, d375846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39352 q selected
    | true =>
      simp only [d375760, d375846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d375761 q = 1) : d375847 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d375761, d375847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d375761, d375847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d375762 q = 1) : d375848 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d375762, d375848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d375762, d375848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d375763 q = 1) : d375849 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d375763, d375849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d375763, d375849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d375764 q = 1) : d375850 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d375764, d375850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d375764, d375850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d375765 q = 1) : d375851 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d375765, d375851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d375765, d375851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39354 (p : Pattern) (selected : d375771 p = 1) : d375857 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d375766 q = 1) : d375852 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d375766, d375852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39353 q selected
    | true =>
      simp only [d375766, d375852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d375767 q = 1) : d375853 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d375767, d375853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d375767, d375853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d375768 q = 1) : d375854 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d375768, d375854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d375768, d375854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d375769 q = 1) : d375855 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d375769, d375855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d375769, d375855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d375770 q = 1) : d375856 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d375770, d375856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d375770, d375856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d375771 q = 1) : d375857 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d375771, d375857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d375771, d375857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39355 (p : Pattern) (selected : d375777 p = 1) : d375863 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d375772 q = 1) : d375858 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d375772, d375858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39354 q selected
    | true =>
      simp only [d375772, d375858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d375773 q = 1) : d375859 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d375773, d375859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d375773, d375859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d375774 q = 1) : d375860 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d375774, d375860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d375774, d375860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d375775 q = 1) : d375861 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d375775, d375861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d375775, d375861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d375776 q = 1) : d375862 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d375776, d375862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d375776, d375862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d375777 q = 1) : d375863 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d375777, d375863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d375777, d375863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39356 (p : Pattern) (selected : d376291 p = 0) : d377675 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d253269 q = 0) : d253268 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d253269, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253269, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d351901 q = 0) : d354133 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d351901, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351901, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376290 q = 0) : d377674 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d376290, d377674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376290, d377674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d351902 q = 0) : d354134 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d351902, d354134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351902, d354134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376291 q = 0) : d377675 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d376291, d377675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376291, d377675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39357 (p : Pattern) (selected : d376297 p = 0) : d377681 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376292 q = 0) : d377676 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376292, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39356 q selected
    | true =>
      simp only [d376292, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376293 q = 0) : d377677 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376293, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376293, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d351904 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36591 q selected
    | true =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351905 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376294 q = 0) : d377678 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376294, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376294, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351906 q = 0) : d354138 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d351906, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351906, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376295 q = 0) : d377679 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376295, d377679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376295, d377679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376296 q = 0) : d377680 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376296, d377680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376296, d377680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d351907 q = 0) : d354139 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d351907, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d351907, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d351908 q = 0) : d354140 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d351908, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d351908, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376297 q = 0) : d377681 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d376297, d377681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376297, d377681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39358 (p : Pattern) (selected : d376303 p = 0) : d377687 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376298 q = 0) : d377682 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376298, d377682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39357 q selected
    | true =>
      simp only [d376298, d377682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376299 q = 0) : d377683 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376299, d377683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376299, d377683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376300 q = 0) : d377684 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376300, d377684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376300, d377684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376301 q = 0) : d377685 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376301, d377685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376301, d377685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351910 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
    | true =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d351911 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d351912 q = 0) : d354144 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d351912, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351912, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d351913 q = 0) : d354145 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d351913, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d351913, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376302 q = 0) : d377686 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376302, d377686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376302, d377686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d351914 q = 0) : d354146 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d351914, d354146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d351914, d354146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376303 q = 0) : d377687 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376303, d377687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376303, d377687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39359 (p : Pattern) (selected : d376309 p = 0) : d377693 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376304 q = 0) : d377688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376304, d377688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39358 q selected
    | true =>
      simp only [d376304, d377688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36593 q selected
  have h2 (q : Pattern) (selected : d376305 q = 0) : d377689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376305, d377689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376305, d377689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376306 q = 0) : d377690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376306, d377690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376306, d377690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351916 q = 0) : d354148 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d351916, d354148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36593 q selected
    | true =>
      simp only [d351916, d354148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351917 q = 0) : d354149 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d351917, d354149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351917, d354149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351918 q = 0) : d354150 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d351918, d354150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351918, d354150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376307 q = 0) : d377691 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376307, d377691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376307, d377691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d351919 q = 0) : d354151 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d351919, d354151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d351919, d354151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376308 q = 0) : d377692 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376308, d377692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376308, d377692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376309 q = 0) : d377693 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376309, d377693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376309, d377693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39360 (p : Pattern) (selected : d376315 p = 0) : d377699 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376310 q = 0) : d377694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39359 q selected
    | true =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376311 q = 0) : d377695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351922 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36594 q selected
    | true =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351923 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376312 q = 0) : d377696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376312, d377696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376312, d377696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376313 q = 0) : d377697 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376313, d377697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376313, d377697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376314 q = 0) : d377698 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376314, d377698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376314, d377698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376315 q = 0) : d377699 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376315, d377699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376315, d377699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39361 (p : Pattern) (selected : d376321 p = 0) : d377705 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352003 q = 0) : d354235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352003, d354235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36607 q selected
    | true =>
      simp only [d352003, d354235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352004 q = 0) : d354236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352004, d354236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352004, d354236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352005 q = 0) : d354237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352005, d354237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352005, d354237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352006 q = 0) : d354238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352006, d354238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352006, d354238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352010 q = 0) : d354242 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352010, d354242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36608 q selected
    | true =>
      simp only [d352010, d354242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352011 q = 0) : d354243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352011, d354243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352011, d354243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352012 q = 0) : d354244 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352012, d354244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352012, d354244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376316 q = 0) : d377700 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376316, d377700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39360 q selected
    | true =>
      simp only [d376316, d377700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
  have h9 (q : Pattern) (selected : d352069 q = 0) : d354160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352069, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36618 q selected
    | true =>
      simp only [d352069, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d376317 q = 0) : d377701 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376317, d377701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376317, d377701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d351928 q = 0) : d354160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
    | true =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d351929 q = 0) : d354161 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351929, d354161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d351929, d354161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d376318 q = 0) : d377702 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376318, d377702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376318, d377702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d376319 q = 0) : d377703 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376319, d377703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376319, d377703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d376320 q = 0) : d377704 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376320, d377704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376320, d377704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d376321 q = 0) : d377705 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376321, d377705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376321, d377705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro39362 (p : Pattern) (selected : d376322 p = 0) : d377706 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376310 q = 0) : d377694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39359 q selected
    | true =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376311 q = 0) : d377695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351922 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36594 q selected
    | true =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351923 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376312 q = 0) : d377696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376312, d377696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376312, d377696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376313 q = 0) : d377697 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376313, d377697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376313, d377697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376314 q = 0) : d377698 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376314, d377698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376314, d377698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376322 q = 0) : d377706 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376322, d377706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376322, d377706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39363 (p : Pattern) (selected : d376328 p = 0) : d377712 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352003 q = 0) : d354235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352003, d354235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36607 q selected
    | true =>
      simp only [d352003, d354235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352004 q = 0) : d354236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352004, d354236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352004, d354236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352005 q = 0) : d354237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352005, d354237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352005, d354237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352006 q = 0) : d354238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352006, d354238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352006, d354238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352010 q = 0) : d354242 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352010, d354242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36608 q selected
    | true =>
      simp only [d352010, d354242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352011 q = 0) : d354243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352011, d354243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352011, d354243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352012 q = 0) : d354244 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352012, d354244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352012, d354244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376316 q = 0) : d377700 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376316, d377700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39360 q selected
    | true =>
      simp only [d376316, d377700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
  have h9 (q : Pattern) (selected : d352069 q = 0) : d354160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352069, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36618 q selected
    | true =>
      simp only [d352069, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d376317 q = 0) : d377701 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376317, d377701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376317, d377701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d351928 q = 0) : d354160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
    | true =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d351929 q = 0) : d354161 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351929, d354161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d351929, d354161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d376318 q = 0) : d377702 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376318, d377702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376318, d377702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d376319 q = 0) : d377703 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376319, d377703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376319, d377703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d376320 q = 0) : d377704 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376320, d377704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376320, d377704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d352076 q = 0) : d354279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352076, d354279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36620 q selected
    | true =>
      simp only [d352076, d354279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d352077 q = 0) : d354280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352077, d354280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352077, d354280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d352078 q = 0) : d354281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352078, d354281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d352078, d354281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d352079 q = 0) : d354282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352079, d354282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352079, d354282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d352081 q = 0) : d354284 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352081, d354284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36621 q selected
    | true =>
      simp only [d352081, d354284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d352082 q = 0) : d354285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352082, d354285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352082, d354285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d352083 q = 0) : d354286 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352083, d354286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d352083, d354286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d376323 q = 0) : d377707 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376323, d377707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39362 q selected
    | true =>
      simp only [d376323, d377707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36597 q selected
  have h24 (q : Pattern) (selected : d352087 q = 0) : d354167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352087, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36623 q selected
    | true =>
      simp only [d352087, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d376324 q = 0) : d377708 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376324, d377708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d376324, d377708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d351935 q = 0) : d354167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351935, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36597 q selected
    | true =>
      simp only [d351935, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d351936 q = 0) : d354168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351936, d354168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d351936, d354168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d376325 q = 0) : d377709 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376325, d377709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d376325, d377709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d376326 q = 0) : d377710 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376326, d377710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d376326, d377710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d376327 q = 0) : d377711 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376327, d377711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d376327, d377711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d376328 q = 0) : d377712 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376328, d377712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d376328, d377712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro39364 (p : Pattern) (selected : d376335 p = 0) : d377719 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376323 q = 0) : d377707 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376323, d377707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39362 q selected
    | true =>
      simp only [d376323, d377707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36597 q selected
  have h2 (q : Pattern) (selected : d352087 q = 0) : d354167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352087, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36623 q selected
    | true =>
      simp only [d352087, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376324 q = 0) : d377708 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376324, d377708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376324, d377708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351935 q = 0) : d354167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351935, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36597 q selected
    | true =>
      simp only [d351935, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351936 q = 0) : d354168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351936, d354168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351936, d354168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376325 q = 0) : d377709 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376325, d377709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376325, d377709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376333 q = 0) : d377717 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376333, d377717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376333, d377717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376334 q = 0) : d377718 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376334, d377718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376334, d377718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376335 q = 0) : d377719 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376335, d377719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376335, d377719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro39365 (p : Pattern) (selected : d376346 p = 0) : d377730 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376341 q = 0) : d377725 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376341, d377725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376341, d377725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39357 q selected
  have h2 (q : Pattern) (selected : d376298 q = 0) : d377682 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376298, d377682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39357 q selected
    | true =>
      simp only [d376298, d377682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376342 q = 0) : d377726 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376342, d377726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376342, d377726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376299 q = 0) : d377683 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376299, d377683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376299, d377683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376343 q = 0) : d377727 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376343, d377727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376343, d377727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376344 q = 0) : d377728 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376344, d377728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376344, d377728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d351951 q = 0) : d354183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351951, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351951, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
  have h8 (q : Pattern) (selected : d351910 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
    | true =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d351952 q = 0) : d354184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351952, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d351952, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d351911 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d351953 q = 0) : d354185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d351953, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d351953, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d351954 q = 0) : d354186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d351954, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d351954, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d376345 q = 0) : d377729 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376345, d377729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376345, d377729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d351955 q = 0) : d354187 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d351955, d354187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d351955, d354187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d376346 q = 0) : d377730 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376346, d377730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376346, d377730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro39366 (p : Pattern) (selected : d376352 p = 0) : d377736 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376347 q = 0) : d377731 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376347, d377731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39365 q selected
    | true =>
      simp only [d376347, d377731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36600 q selected
  have h2 (q : Pattern) (selected : d376348 q = 0) : d377732 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376348, d377732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376348, d377732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376349 q = 0) : d377733 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376349, d377733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376349, d377733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351957 q = 0) : d354189 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d351957, d354189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36600 q selected
    | true =>
      simp only [d351957, d354189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351958 q = 0) : d354190 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d351958, d354190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351958, d354190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351959 q = 0) : d354191 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d351959, d354191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351959, d354191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376350 q = 0) : d377734 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376350, d377734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376350, d377734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d351960 q = 0) : d354192 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d351960, d354192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d351960, d354192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376351 q = 0) : d377735 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376351, d377735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376351, d377735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376352 q = 0) : d377736 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376352, d377736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376352, d377736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39367 (p : Pattern) (selected : d376358 p = 0) : d377742 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376353 q = 0) : d377737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376353, d377737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39366 q selected
    | true =>
      simp only [d376353, d377737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376354 q = 0) : d377738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376354, d377738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376354, d377738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351963 q = 0) : d354195 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351963, d354195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36601 q selected
    | true =>
      simp only [d351963, d354195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351964 q = 0) : d354196 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351964, d354196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351964, d354196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376355 q = 0) : d377739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376355, d377739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376355, d377739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376356 q = 0) : d377740 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376356, d377740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376356, d377740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376357 q = 0) : d377741 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376357, d377741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376357, d377741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376358 q = 0) : d377742 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376358, d377742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376358, d377742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39368 (p : Pattern) (selected : d376364 p = 0) : d377748 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376359 q = 0) : d377743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376359, d377743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39367 q selected
    | true =>
      simp only [d376359, d377743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36602 q selected
  have h2 (q : Pattern) (selected : d352144 q = 0) : d354201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352144, d354201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36632 q selected
    | true =>
      simp only [d352144, d354201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376360 q = 0) : d377744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376360, d377744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376360, d377744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351969 q = 0) : d354201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351969, d354201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36602 q selected
    | true =>
      simp only [d351969, d354201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351970 q = 0) : d354202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351970, d354202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351970, d354202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376361 q = 0) : d377745 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376361, d377745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376361, d377745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376362 q = 0) : d377746 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376362, d377746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376362, d377746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376363 q = 0) : d377747 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376363, d377747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376363, d377747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376364 q = 0) : d377748 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376364, d377748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376364, d377748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro39369 (p : Pattern) (selected : d376370 p = 0) : d377754 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351991 q = 0) : d354223 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d351991, d354223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351991, d354223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36605 q selected
  have h2 (q : Pattern) (selected : d351992 q = 0) : d354224 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d351992, d354224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d351992, d354224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d351998 q = 0) : d354230 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d351998, d354230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36605 q selected
    | true =>
      simp only [d351998, d354230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36606 q selected
  have h4 (q : Pattern) (selected : d351999 q = 0) : d354231 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d351999, d354231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351999, d354231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352000 q = 0) : d354232 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d352000, d354232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352000, d354232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376329 q = 0) : d377713 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376329, d377713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39361 q selected
    | true =>
      simp only [d376329, d377713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39363 q selected
  have h7 (q : Pattern) (selected : d352095 q = 0) : d354296 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352095, d354296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36625 q selected
    | true =>
      simp only [d352095, d354296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376330 q = 0) : d377714 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376330, d377714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376330, d377714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376331 q = 0) : d377715 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376331, d377715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376331, d377715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d376332 q = 0) : d377716 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d376332, d377716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376332, d377716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d376336 q = 0) : d377720 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376336, d377720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376336, d377720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39364 q selected
  have h12 (q : Pattern) (selected : d376337 q = 0) : d377721 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376337, d377721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d376337, d377721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d376338 q = 0) : d377722 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376338, d377722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376338, d377722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d376339 q = 0) : d377723 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d376339, d377723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376339, d377723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d376340 q = 0) : d377724 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d376340, d377724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376340, d377724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d376365 q = 0) : d377749 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376365, d377749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376365, d377749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39368 q selected
  have h17 (q : Pattern) (selected : d376366 q = 0) : d377750 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376366, d377750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d376366, d377750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d376367 q = 0) : d377751 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376367, d377751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d376367, d377751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d376368 q = 0) : d377752 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d376368, d377752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d376368, d377752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d376369 q = 0) : d377753 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d376369, d377753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d376369, d377753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d376370 q = 0) : d377754 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d376370, d377754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d376370, d377754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro39370 (p : Pattern) (selected : d376376 p = 0) : d377760 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351981 q = 0) : d354213 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d351981, d354213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351981, d354213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36604 q selected
  have h2 (q : Pattern) (selected : d351982 q = 0) : d354214 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d351982, d354214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351982, d354214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351983 q = 0) : d354215 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d351983, d354215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351983, d354215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351984 q = 0) : d354216 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d351984, d354216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351984, d354216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d351985 q = 0) : d354217 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d351985, d354217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351985, d354217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376371 q = 0) : d377755 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d376371, d377755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376371, d377755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39369 q selected
  have h7 (q : Pattern) (selected : d376372 q = 0) : d377756 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d376372, d377756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376372, d377756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376373 q = 0) : d377757 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d376373, d377757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376373, d377757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376374 q = 0) : d377758 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d376374, d377758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376374, d377758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376375 q = 0) : d377759 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d376375, d377759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376375, d377759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d376376 q = 0) : d377760 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d376376, d377760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376376, d377760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39371 (p : Pattern) (selected : d376381 p = 0) : d377765 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376316 q = 0) : d377700 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376316, d377700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39360 q selected
    | true =>
      simp only [d376316, d377700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
  have h2 (q : Pattern) (selected : d376377 q = 0) : d377761 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376377, d377761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376377, d377761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376378 q = 0) : d377762 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376378, d377762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376378, d377762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376379 q = 0) : d377763 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376379, d377763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376379, d377763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376380 q = 0) : d377764 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376380, d377764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376380, d377764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376381 q = 0) : d377765 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376381, d377765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376381, d377765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39372 (p : Pattern) (selected : d376388 p = 0) : d377772 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376316 q = 0) : d377700 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376316, d377700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39360 q selected
    | true =>
      simp only [d376316, d377700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
  have h2 (q : Pattern) (selected : d376377 q = 0) : d377761 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376377, d377761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376377, d377761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376378 q = 0) : d377762 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376378, d377762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376378, d377762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376379 q = 0) : d377763 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376379, d377763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376379, d377763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376380 q = 0) : d377764 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376380, d377764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376380, d377764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376323 q = 0) : d377707 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376323, d377707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39362 q selected
    | true =>
      simp only [d376323, d377707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36597 q selected
  have h7 (q : Pattern) (selected : d376384 q = 0) : d377768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376384, d377768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376384, d377768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376385 q = 0) : d377769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376385, d377769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376385, d377769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376386 q = 0) : d377770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376386, d377770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376386, d377770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376387 q = 0) : d377771 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376387, d377771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376387, d377771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d376388 q = 0) : d377772 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376388, d377772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376388, d377772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39373 (p : Pattern) (selected : d376393 p = 0) : d377777 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376310 q = 0) : d377694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39359 q selected
    | true =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376311 q = 0) : d377695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351922 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36594 q selected
    | true =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351923 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376312 q = 0) : d377696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376312, d377696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376312, d377696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376313 q = 0) : d377697 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376313, d377697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376313, d377697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376392 q = 0) : d377776 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376392, d377776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376392, d377776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376393 q = 0) : d377777 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376393, d377777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376393, d377777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39374 (p : Pattern) (selected : d376400 p = 0) : d377784 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376310 q = 0) : d377694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39359 q selected
    | true =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376311 q = 0) : d377695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351922 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36594 q selected
    | true =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351923 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376312 q = 0) : d377696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376312, d377696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376312, d377696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376398 q = 0) : d377782 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376398, d377782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376398, d377782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376399 q = 0) : d377783 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376399, d377783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376399, d377783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376400 q = 0) : d377784 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376400, d377784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376400, d377784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39375 (p : Pattern) (selected : d376404 p = 0) : d377788 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d253269 q = 0) : d253268 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d253269, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253269, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d351901 q = 0) : d354133 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d351901, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351901, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376290 q = 0) : d377674 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d376290, d377674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376290, d377674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376404 q = 0) : d377788 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d376404, d377788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376404, d377788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro39376 (p : Pattern) (selected : d376410 p = 0) : d377794 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376405 q = 0) : d377789 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376405, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39375 q selected
    | true =>
      simp only [d376405, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376406 q = 0) : d377790 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376406, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376406, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376292 q = 0) : d377676 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376292, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39356 q selected
    | true =>
      simp only [d376292, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376293 q = 0) : d377677 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376293, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376293, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376407 q = 0) : d377791 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376407, d377791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376407, d377791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351904 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36591 q selected
    | true =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d351905 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376294 q = 0) : d377678 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376294, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376294, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376408 q = 0) : d377792 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376408, d377792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376408, d377792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376409 q = 0) : d377793 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376409, d377793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376409, d377793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d351906 q = 0) : d354138 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d351906, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d351906, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d376295 q = 0) : d377679 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376295, d377679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376295, d377679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d376296 q = 0) : d377680 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376296, d377680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376296, d377680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d376410 q = 0) : d377794 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d376410, d377794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376410, d377794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro39377 (p : Pattern) (selected : d376418 p = 0) : d377802 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376292 q = 0) : d377676 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376292, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39356 q selected
    | true =>
      simp only [d376292, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376293 q = 0) : d377677 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376293, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376293, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d351904 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36591 q selected
    | true =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351905 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376294 q = 0) : d377678 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376294, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376294, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376416 q = 0) : d377800 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376416, d377800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376416, d377800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376417 q = 0) : d377801 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376417, d377801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376417, d377801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d351906 q = 0) : d354138 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d351906, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351906, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d351907 q = 0) : d354139 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d351907, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d351907, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d351908 q = 0) : d354140 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d351908, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d351908, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376418 q = 0) : d377802 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d376418, d377802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376418, d377802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39378 (p : Pattern) (selected : d376424 p = 0) : d377808 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376411 q = 0) : d377795 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376411, d377795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39376 q selected
    | true =>
      simp only [d376411, d377795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376412 q = 0) : d377796 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376412, d377796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376412, d377796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376413 q = 0) : d377797 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376413, d377797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376413, d377797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376414 q = 0) : d377798 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376414, d377798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376414, d377798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376298 q = 0) : d377682 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376298, d377682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39357 q selected
    | true =>
      simp only [d376298, d377682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376299 q = 0) : d377683 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376299, d377683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376299, d377683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376300 q = 0) : d377684 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376300, d377684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376300, d377684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376301 q = 0) : d377685 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376301, d377685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376301, d377685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376415 q = 0) : d377799 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376415, d377799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376415, d377799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376419 q = 0) : d377803 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376419, d377803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39377 q selected
    | true =>
      simp only [d376419, d377803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376420 q = 0) : d377804 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376420, d377804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376420, d377804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d376421 q = 0) : d377805 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376421, d377805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376421, d377805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d376422 q = 0) : d377806 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376422, d377806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376422, d377806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d351910 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
    | true =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d351911 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d351912 q = 0) : d354144 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d351912, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351912, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d351913 q = 0) : d354145 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d351913, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d351913, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d376423 q = 0) : d377807 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376423, d377807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376423, d377807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d376424 q = 0) : d377808 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376424, d377808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376424, d377808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro39379 (p : Pattern) (selected : d376430 p = 0) : d377814 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376425 q = 0) : d377809 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376425, d377809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39378 q selected
    | true =>
      simp only [d376425, d377809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39358 q selected
  have h2 (q : Pattern) (selected : d376426 q = 0) : d377810 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376426, d377810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376426, d377810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376427 q = 0) : d377811 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376427, d377811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376427, d377811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376304 q = 0) : d377688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376304, d377688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39358 q selected
    | true =>
      simp only [d376304, d377688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36593 q selected
  have h5 (q : Pattern) (selected : d376305 q = 0) : d377689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376305, d377689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376305, d377689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376306 q = 0) : d377690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376306, d377690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376306, d377690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376428 q = 0) : d377812 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376428, d377812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376428, d377812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d351916 q = 0) : d354148 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d351916, d354148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36593 q selected
    | true =>
      simp only [d351916, d354148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d351917 q = 0) : d354149 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d351917, d354149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351917, d354149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d351918 q = 0) : d354150 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d351918, d354150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351918, d354150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d376307 q = 0) : d377691 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376307, d377691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376307, d377691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d376429 q = 0) : d377813 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376429, d377813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376429, d377813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d376430 q = 0) : d377814 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376430, d377814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376430, d377814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro39380 (p : Pattern) (selected : d376436 p = 0) : d377820 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376431 q = 0) : d377815 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376431, d377815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39379 q selected
    | true =>
      simp only [d376431, d377815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376432 q = 0) : d377816 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376432, d377816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376432, d377816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376310 q = 0) : d377694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39359 q selected
    | true =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376311 q = 0) : d377695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376433 q = 0) : d377817 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376433, d377817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376433, d377817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376434 q = 0) : d377818 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376434, d377818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376434, d377818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376435 q = 0) : d377819 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376435, d377819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376435, d377819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376436 q = 0) : d377820 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376436, d377820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376436, d377820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39381 (p : Pattern) (selected : d376439 p = 0) : d377675 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d352041 q = 0) : d253268 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d352041, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352041, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352042 q = 0) : d354133 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d352042, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352042, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376438 q = 0) : d377674 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d376438, d377674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376438, d377674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352043 q = 0) : d354134 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d352043, d354134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352043, d354134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376439 q = 0) : d377675 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d376439, d377675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376439, d377675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39382 (p : Pattern) (selected : d376445 p = 0) : d377681 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376440 q = 0) : d377676 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376440, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39381 q selected
    | true =>
      simp only [d376440, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376441 q = 0) : d377677 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376441, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376441, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352045 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36614 q selected
    | true =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352046 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376442 q = 0) : d377678 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376442, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376442, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352047 q = 0) : d354138 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352047, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352047, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376443 q = 0) : d377679 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376443, d377679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376443, d377679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376444 q = 0) : d377680 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376444, d377680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376444, d377680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352048 q = 0) : d354139 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352048, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352048, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d352049 q = 0) : d354140 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352049, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352049, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376445 q = 0) : d377681 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d376445, d377681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376445, d377681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39383 (p : Pattern) (selected : d376451 p = 0) : d377687 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376446 q = 0) : d377682 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376446, d377682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39382 q selected
    | true =>
      simp only [d376446, d377682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376447 q = 0) : d377683 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376447, d377683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376447, d377683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376448 q = 0) : d377684 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376448, d377684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376448, d377684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376449 q = 0) : d377685 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376449, d377685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376449, d377685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352051 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36615 q selected
    | true =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352052 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352053 q = 0) : d354144 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352053, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352053, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352054 q = 0) : d354145 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352054, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352054, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376450 q = 0) : d377686 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376450, d377686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376450, d377686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352055 q = 0) : d354146 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352055, d354146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352055, d354146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376451 q = 0) : d377687 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376451, d377687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376451, d377687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39384 (p : Pattern) (selected : d376457 p = 0) : d377693 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376452 q = 0) : d377688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376452, d377688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39383 q selected
    | true =>
      simp only [d376452, d377688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36616 q selected
  have h2 (q : Pattern) (selected : d376453 q = 0) : d377689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376453, d377689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376453, d377689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376454 q = 0) : d377690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376454, d377690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376454, d377690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352057 q = 0) : d354148 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352057, d354148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36616 q selected
    | true =>
      simp only [d352057, d354148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352058 q = 0) : d354149 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352058, d354149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352058, d354149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352059 q = 0) : d354150 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352059, d354150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352059, d354150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376455 q = 0) : d377691 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376455, d377691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376455, d377691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352060 q = 0) : d354151 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352060, d354151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352060, d354151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376456 q = 0) : d377692 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376456, d377692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376456, d377692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376457 q = 0) : d377693 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376457, d377693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376457, d377693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39385 (p : Pattern) (selected : d376463 p = 0) : d377699 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376458 q = 0) : d377694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376458, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39384 q selected
    | true =>
      simp only [d376458, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376459 q = 0) : d377695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376459, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376459, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352063 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352063, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36617 q selected
    | true =>
      simp only [d352063, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352064 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352064, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352064, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376460 q = 0) : d377696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376460, d377696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376460, d377696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376461 q = 0) : d377697 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376461, d377697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376461, d377697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376462 q = 0) : d377698 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376462, d377698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376462, d377698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376463 q = 0) : d377699 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376463, d377699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376463, d377699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39386 (p : Pattern) (selected : d376469 p = 0) : d377826 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376310 q = 0) : d377694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39359 q selected
    | true =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376311 q = 0) : d377695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376466 q = 0) : d377823 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376466, d377823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376466, d377823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376467 q = 0) : d377824 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376467, d377824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376467, d377824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376468 q = 0) : d377825 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376468, d377825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376468, d377825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376469 q = 0) : d377826 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376469, d377826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376469, d377826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39387 (p : Pattern) (selected : d376475 p = 0) : d377832 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376394 q = 0) : d377778 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376394, d377778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39373 q selected
    | true =>
      simp only [d376394, d377778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36607 q selected
  have h2 (q : Pattern) (selected : d376395 q = 0) : d377779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376395, d377779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376395, d377779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376396 q = 0) : d377780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376396, d377780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376396, d377780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376397 q = 0) : d377781 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376397, d377781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376397, d377781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376401 q = 0) : d377785 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376401, d377785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39374 q selected
    | true =>
      simp only [d376401, d377785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36608 q selected
  have h6 (q : Pattern) (selected : d376402 q = 0) : d377786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376402, d377786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376402, d377786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376403 q = 0) : d377787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376403, d377787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376403, d377787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376437 q = 0) : d377821 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376437, d377821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39380 q selected
    | true =>
      simp only [d376437, d377821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39360 q selected
  have h9 (q : Pattern) (selected : d376464 q = 0) : d377700 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376464, d377700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39385 q selected
    | true =>
      simp only [d376464, d377700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36618 q selected
  have h10 (q : Pattern) (selected : d376465 q = 0) : d377822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376465, d377822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376465, d377822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d376470 q = 0) : d377827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376470, d377827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39386 q selected
    | true =>
      simp only [d376470, d377827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d376471 q = 0) : d377828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376471, d377828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d376471, d377828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d376472 q = 0) : d377829 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376472, d377829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376472, d377829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d376473 q = 0) : d377830 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376473, d377830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376473, d377830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d376474 q = 0) : d377831 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376474, d377831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376474, d377831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d376475 q = 0) : d377832 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376475, d377832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376475, d377832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro39388 (p : Pattern) (selected : d376476 p = 0) : d377833 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376310 q = 0) : d377694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39359 q selected
    | true =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376311 q = 0) : d377695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351922 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36594 q selected
    | true =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351923 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376312 q = 0) : d377696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376312, d377696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376312, d377696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376313 q = 0) : d377697 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376313, d377697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376313, d377697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376392 q = 0) : d377776 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376392, d377776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376392, d377776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376476 q = 0) : d377833 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376476, d377833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376476, d377833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39389 (p : Pattern) (selected : d376481 p = 0) : d377838 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376310 q = 0) : d377694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39359 q selected
    | true =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376311 q = 0) : d377695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351922 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36594 q selected
    | true =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351923 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376312 q = 0) : d377696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376312, d377696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376312, d377696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376398 q = 0) : d377782 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376398, d377782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376398, d377782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376399 q = 0) : d377783 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376399, d377783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376399, d377783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376481 q = 0) : d377838 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376481, d377838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376481, d377838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39390 (p : Pattern) (selected : d376485 p = 0) : d377842 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376431 q = 0) : d377815 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376431, d377815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39379 q selected
    | true =>
      simp only [d376431, d377815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376432 q = 0) : d377816 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376432, d377816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376432, d377816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376310 q = 0) : d377694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39359 q selected
    | true =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376311 q = 0) : d377695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376433 q = 0) : d377817 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376433, d377817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376433, d377817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376434 q = 0) : d377818 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376434, d377818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376434, d377818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376435 q = 0) : d377819 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376435, d377819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376435, d377819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376485 q = 0) : d377842 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376485, d377842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376485, d377842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39391 (p : Pattern) (selected : d376487 p = 0) : d377706 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376458 q = 0) : d377694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376458, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39384 q selected
    | true =>
      simp only [d376458, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376459 q = 0) : d377695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376459, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376459, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352063 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352063, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36617 q selected
    | true =>
      simp only [d352063, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352064 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352064, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352064, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376460 q = 0) : d377696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376460, d377696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376460, d377696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376461 q = 0) : d377697 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376461, d377697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376461, d377697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376462 q = 0) : d377698 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376462, d377698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376462, d377698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376487 q = 0) : d377706 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376487, d377706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376487, d377706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39392 (p : Pattern) (selected : d376490 p = 0) : d377845 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376310 q = 0) : d377694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39359 q selected
    | true =>
      simp only [d376310, d377694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376311 q = 0) : d377695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376311, d377695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376466 q = 0) : d377823 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376466, d377823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376466, d377823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376467 q = 0) : d377824 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376467, d377824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376467, d377824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376468 q = 0) : d377825 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376468, d377825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376468, d377825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376490 q = 0) : d377845 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376490, d377845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376490, d377845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39393 (p : Pattern) (selected : d376496 p = 0) : d377851 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376394 q = 0) : d377778 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376394, d377778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39373 q selected
    | true =>
      simp only [d376394, d377778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36607 q selected
  have h2 (q : Pattern) (selected : d376395 q = 0) : d377779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376395, d377779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376395, d377779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376396 q = 0) : d377780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376396, d377780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376396, d377780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376397 q = 0) : d377781 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376397, d377781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376397, d377781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376401 q = 0) : d377785 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376401, d377785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39374 q selected
    | true =>
      simp only [d376401, d377785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36608 q selected
  have h6 (q : Pattern) (selected : d376402 q = 0) : d377786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376402, d377786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376402, d377786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376403 q = 0) : d377787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376403, d377787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376403, d377787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376437 q = 0) : d377821 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376437, d377821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39380 q selected
    | true =>
      simp only [d376437, d377821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39360 q selected
  have h9 (q : Pattern) (selected : d376464 q = 0) : d377700 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376464, d377700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39385 q selected
    | true =>
      simp only [d376464, d377700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36618 q selected
  have h10 (q : Pattern) (selected : d376465 q = 0) : d377822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376465, d377822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376465, d377822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d376470 q = 0) : d377827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376470, d377827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39386 q selected
    | true =>
      simp only [d376470, d377827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d376471 q = 0) : d377828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376471, d377828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d376471, d377828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d376472 q = 0) : d377829 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376472, d377829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376472, d377829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d376473 q = 0) : d377830 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376473, d377830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376473, d377830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d376474 q = 0) : d377831 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376474, d377831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376474, d377831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d376477 q = 0) : d377834 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376477, d377834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39388 q selected
    | true =>
      simp only [d376477, d377834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36620 q selected
  have h17 (q : Pattern) (selected : d376478 q = 0) : d377835 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376478, d377835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376478, d377835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d376479 q = 0) : d377836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376479, d377836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d376479, d377836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d376480 q = 0) : d377837 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376480, d377837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376480, d377837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d376482 q = 0) : d377839 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376482, d377839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39389 q selected
    | true =>
      simp only [d376482, d377839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36621 q selected
  have h21 (q : Pattern) (selected : d376483 q = 0) : d377840 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376483, d377840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376483, d377840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d376484 q = 0) : d377841 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376484, d377841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d376484, d377841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d376486 q = 0) : d377843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376486, d377843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39390 q selected
    | true =>
      simp only [d376486, d377843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39362 q selected
  have h24 (q : Pattern) (selected : d376488 q = 0) : d377707 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376488, d377707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39391 q selected
    | true =>
      simp only [d376488, d377707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36623 q selected
  have h25 (q : Pattern) (selected : d376489 q = 0) : d377844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376489, d377844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d376489, d377844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d376491 q = 0) : d377846 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376491, d377846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39392 q selected
    | true =>
      simp only [d376491, d377846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d376492 q = 0) : d377847 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376492, d377847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d376492, d377847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d376493 q = 0) : d377848 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376493, d377848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d376493, d377848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d376494 q = 0) : d377849 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376494, d377849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d376494, d377849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d376495 q = 0) : d377850 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376495, d377850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d376495, d377850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d376496 q = 0) : d377851 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376496, d377851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d376496, d377851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro39394 (p : Pattern) (selected : d376498 p = 0) : d377853 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376316 q = 0) : d377700 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376316, d377700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39360 q selected
    | true =>
      simp only [d376316, d377700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
  have h2 (q : Pattern) (selected : d376377 q = 0) : d377761 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376377, d377761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376377, d377761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376378 q = 0) : d377762 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376378, d377762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376378, d377762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376379 q = 0) : d377763 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376379, d377763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376379, d377763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376380 q = 0) : d377764 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376380, d377764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376380, d377764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351928 q = 0) : d354160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
    | true =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d351986 q = 0) : d354218 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351986, d354218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351986, d354218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d351987 q = 0) : d354219 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d351987, d354219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d351987, d354219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d351988 q = 0) : d354220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d351988, d354220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351988, d354220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d351989 q = 0) : d354221 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d351989, d354221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351989, d354221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d376498 q = 0) : d377853 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376498, d377853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376498, d377853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39395 (p : Pattern) (selected : d376505 p = 0) : d377860 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376486 q = 0) : d377843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376486, d377843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39390 q selected
    | true =>
      simp only [d376486, d377843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39362 q selected
  have h2 (q : Pattern) (selected : d376488 q = 0) : d377707 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376488, d377707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39391 q selected
    | true =>
      simp only [d376488, d377707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36623 q selected
  have h3 (q : Pattern) (selected : d376489 q = 0) : d377844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376489, d377844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376489, d377844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376491 q = 0) : d377846 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376491, d377846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39392 q selected
    | true =>
      simp only [d376491, d377846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376492 q = 0) : d377847 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376492, d377847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376492, d377847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376493 q = 0) : d377848 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376493, d377848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376493, d377848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376503 q = 0) : d377858 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376503, d377858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376503, d377858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376504 q = 0) : d377859 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376504, d377859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376504, d377859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376505 q = 0) : d377860 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376505, d377860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376505, d377860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro39396 (p : Pattern) (selected : d376521 p = 0) : d377876 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376511 q = 0) : d377866 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376511, d377866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376511, d377866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39376 q selected
  have h2 (q : Pattern) (selected : d376411 q = 0) : d377795 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376411, d377795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39376 q selected
    | true =>
      simp only [d376411, d377795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376512 q = 0) : d377867 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376512, d377867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376512, d377867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376412 q = 0) : d377796 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376412, d377796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376412, d377796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376513 q = 0) : d377868 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376513, d377868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376513, d377868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376514 q = 0) : d377869 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376514, d377869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376514, d377869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376341 q = 0) : d377725 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376341, d377725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376341, d377725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39357 q selected
  have h8 (q : Pattern) (selected : d376298 q = 0) : d377682 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376298, d377682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39357 q selected
    | true =>
      simp only [d376298, d377682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376342 q = 0) : d377726 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376342, d377726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376342, d377726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376299 q = 0) : d377683 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376299, d377683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376299, d377683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376343 q = 0) : d377727 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376343, d377727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376343, d377727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d376344 q = 0) : d377728 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376344, d377728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d376344, d377728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d376515 q = 0) : d377870 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376515, d377870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376515, d377870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d376516 q = 0) : d377871 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376516, d377871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376516, d377871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39377 q selected
  have h15 (q : Pattern) (selected : d376419 q = 0) : d377803 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376419, d377803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39377 q selected
    | true =>
      simp only [d376419, d377803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d376517 q = 0) : d377872 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376517, d377872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d376517, d377872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d376420 q = 0) : d377804 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376420, d377804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d376420, d377804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d376518 q = 0) : d377873 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376518, d377873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d376518, d377873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d376519 q = 0) : d377874 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376519, d377874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d376519, d377874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d351951 q = 0) : d354183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351951, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351951, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
  have h21 (q : Pattern) (selected : d351910 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
    | true =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d351952 q = 0) : d354184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351952, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d351952, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d351911 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d351953 q = 0) : d354185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d351953, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d351953, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d351954 q = 0) : d354186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d351954, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d351954, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d376520 q = 0) : d377875 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376520, d377875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d376520, d377875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d376521 q = 0) : d377876 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376521, d377876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376521, d377876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro39397 (p : Pattern) (selected : d376527 p = 0) : d377882 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376522 q = 0) : d377877 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376522, d377877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39396 q selected
    | true =>
      simp only [d376522, d377877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39365 q selected
  have h2 (q : Pattern) (selected : d376523 q = 0) : d377878 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376523, d377878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376523, d377878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376524 q = 0) : d377879 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376524, d377879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376524, d377879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376347 q = 0) : d377731 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376347, d377731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39365 q selected
    | true =>
      simp only [d376347, d377731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36600 q selected
  have h5 (q : Pattern) (selected : d376348 q = 0) : d377732 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376348, d377732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376348, d377732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376349 q = 0) : d377733 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376349, d377733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376349, d377733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376525 q = 0) : d377880 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376525, d377880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376525, d377880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d351957 q = 0) : d354189 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d351957, d354189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36600 q selected
    | true =>
      simp only [d351957, d354189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d351958 q = 0) : d354190 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d351958, d354190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351958, d354190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d351959 q = 0) : d354191 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d351959, d354191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351959, d354191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d376350 q = 0) : d377734 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376350, d377734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376350, d377734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d376526 q = 0) : d377881 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376526, d377881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376526, d377881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d376527 q = 0) : d377882 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376527, d377882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376527, d377882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro39398 (p : Pattern) (selected : d376533 p = 0) : d377888 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376528 q = 0) : d377883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376528, d377883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39397 q selected
    | true =>
      simp only [d376528, d377883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376529 q = 0) : d377884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376529, d377884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376529, d377884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376353 q = 0) : d377737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376353, d377737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39366 q selected
    | true =>
      simp only [d376353, d377737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376354 q = 0) : d377738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376354, d377738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376354, d377738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376530 q = 0) : d377885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376530, d377885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376530, d377885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376531 q = 0) : d377886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376531, d377886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376531, d377886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376532 q = 0) : d377887 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376532, d377887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376532, d377887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376533 q = 0) : d377888 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376533, d377888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376533, d377888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39399 (p : Pattern) (selected : d376540 p = 0) : d377730 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376535 q = 0) : d377725 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376535, d377725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376535, d377725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39382 q selected
  have h2 (q : Pattern) (selected : d376446 q = 0) : d377682 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376446, d377682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39382 q selected
    | true =>
      simp only [d376446, d377682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376536 q = 0) : d377726 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376536, d377726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376536, d377726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376447 q = 0) : d377683 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376447, d377683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376447, d377683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376537 q = 0) : d377727 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376537, d377727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376537, d377727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376538 q = 0) : d377728 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376538, d377728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376538, d377728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352126 q = 0) : d354183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352126, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352126, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36615 q selected
  have h8 (q : Pattern) (selected : d352051 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36615 q selected
    | true =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352127 q = 0) : d354184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352127, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352127, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352052 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352128 q = 0) : d354185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352128, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352128, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d352129 q = 0) : d354186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352129, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d352129, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d376539 q = 0) : d377729 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376539, d377729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376539, d377729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d352130 q = 0) : d354187 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352130, d354187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d352130, d354187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d376540 q = 0) : d377730 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376540, d377730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376540, d377730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro39400 (p : Pattern) (selected : d376546 p = 0) : d377736 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376541 q = 0) : d377731 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376541, d377731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39399 q selected
    | true =>
      simp only [d376541, d377731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36630 q selected
  have h2 (q : Pattern) (selected : d376542 q = 0) : d377732 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376542, d377732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376542, d377732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376543 q = 0) : d377733 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376543, d377733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376543, d377733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352132 q = 0) : d354189 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352132, d354189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36630 q selected
    | true =>
      simp only [d352132, d354189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352133 q = 0) : d354190 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352133, d354190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352133, d354190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352134 q = 0) : d354191 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352134, d354191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352134, d354191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376544 q = 0) : d377734 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376544, d377734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376544, d377734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352135 q = 0) : d354192 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352135, d354192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352135, d354192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376545 q = 0) : d377735 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376545, d377735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376545, d377735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376546 q = 0) : d377736 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376546, d377736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376546, d377736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39401 (p : Pattern) (selected : d376552 p = 0) : d377742 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376547 q = 0) : d377737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376547, d377737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39400 q selected
    | true =>
      simp only [d376547, d377737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376548 q = 0) : d377738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376548, d377738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376548, d377738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352138 q = 0) : d354195 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352138, d354195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36631 q selected
    | true =>
      simp only [d352138, d354195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352139 q = 0) : d354196 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352139, d354196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352139, d354196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376549 q = 0) : d377739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376549, d377739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376549, d377739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376550 q = 0) : d377740 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376550, d377740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376550, d377740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376551 q = 0) : d377741 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376551, d377741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376551, d377741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376552 q = 0) : d377742 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376552, d377742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376552, d377742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39402 (p : Pattern) (selected : d376558 p = 0) : d377894 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376353 q = 0) : d377737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376353, d377737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39366 q selected
    | true =>
      simp only [d376353, d377737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376354 q = 0) : d377738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376354, d377738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376354, d377738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376555 q = 0) : d377891 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376555, d377891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376555, d377891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376556 q = 0) : d377892 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376556, d377892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376556, d377892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376557 q = 0) : d377893 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376557, d377893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376557, d377893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376558 q = 0) : d377894 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376558, d377894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376558, d377894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39403 (p : Pattern) (selected : d376564 p = 0) : d377900 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376534 q = 0) : d377889 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376534, d377889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39398 q selected
    | true =>
      simp only [d376534, d377889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39367 q selected
  have h2 (q : Pattern) (selected : d376553 q = 0) : d377743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376553, d377743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39401 q selected
    | true =>
      simp only [d376553, d377743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36632 q selected
  have h3 (q : Pattern) (selected : d376554 q = 0) : d377890 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376554, d377890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376554, d377890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376559 q = 0) : d377895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376559, d377895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39402 q selected
    | true =>
      simp only [d376559, d377895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376560 q = 0) : d377896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376560, d377896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376560, d377896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376561 q = 0) : d377897 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376561, d377897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376561, d377897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376562 q = 0) : d377898 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376562, d377898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376562, d377898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376563 q = 0) : d377899 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376563, d377899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376563, d377899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376564 q = 0) : d377900 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376564, d377900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376564, d377900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro39404 (p : Pattern) (selected : d376570 p = 0) : d377906 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376382 q = 0) : d377766 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376382, d377766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376382, d377766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39371 q selected
  have h2 (q : Pattern) (selected : d376383 q = 0) : d377767 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376383, d377767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376383, d377767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376389 q = 0) : d377773 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376389, d377773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39371 q selected
    | true =>
      simp only [d376389, d377773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39372 q selected
  have h4 (q : Pattern) (selected : d376390 q = 0) : d377774 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376390, d377774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376390, d377774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376391 q = 0) : d377775 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376391, d377775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376391, d377775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376497 q = 0) : d377852 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376497, d377852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39387 q selected
    | true =>
      simp only [d376497, d377852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39393 q selected
  have h7 (q : Pattern) (selected : d376499 q = 0) : d377854 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376499, d377854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39394 q selected
    | true =>
      simp only [d376499, d377854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36606 q selected
  have h8 (q : Pattern) (selected : d376500 q = 0) : d377855 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376500, d377855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376500, d377855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376501 q = 0) : d377856 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376501, d377856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376501, d377856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d376502 q = 0) : d377857 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d376502, d377857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376502, d377857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d376506 q = 0) : d377861 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376506, d377861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376506, d377861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39395 q selected
  have h12 (q : Pattern) (selected : d352297 q = 0) : d354449 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352297, d354449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352297, d354449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36661 q selected
  have h13 (q : Pattern) (selected : d376507 q = 0) : d377862 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376507, d377862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d376507, d377862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d376508 q = 0) : d377863 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376508, d377863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376508, d377863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d376509 q = 0) : d377864 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d376509, d377864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d376509, d377864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d376510 q = 0) : d377865 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d376510, d377865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376510, d377865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d376565 q = 0) : d377901 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376565, d377901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376565, d377901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39403 q selected
  have h18 (q : Pattern) (selected : d352362 q = 0) : d354495 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352362, d354495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352362, d354495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36670 q selected
  have h19 (q : Pattern) (selected : d376566 q = 0) : d377902 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376566, d377902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d376566, d377902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d376567 q = 0) : d377903 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376567, d377903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d376567, d377903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d376568 q = 0) : d377904 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d376568, d377904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d376568, d377904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d376569 q = 0) : d377905 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d376569, d377905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d376569, d377905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d376570 q = 0) : d377906 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d376570, d377906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d376570, d377906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro39405 (p : Pattern) (selected : d376576 p = 0) : d377912 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376571 q = 0) : d377907 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d376571, d377907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376571, d377907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39404 q selected
  have h2 (q : Pattern) (selected : d376572 q = 0) : d377908 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d376572, d377908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376572, d377908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376573 q = 0) : d377909 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d376573, d377909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376573, d377909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376574 q = 0) : d377910 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d376574, d377910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376574, d377910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376575 q = 0) : d377911 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d376575, d377911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376575, d377911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376576 q = 0) : d377912 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d376576, d377912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376576, d377912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39406 (p : Pattern) (selected : d376580 p = 0) : d377916 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376425 q = 0) : d377809 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376425, d377809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39378 q selected
    | true =>
      simp only [d376425, d377809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39358 q selected
  have h2 (q : Pattern) (selected : d376426 q = 0) : d377810 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376426, d377810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376426, d377810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376427 q = 0) : d377811 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376427, d377811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376427, d377811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376304 q = 0) : d377688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376304, d377688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39358 q selected
    | true =>
      simp only [d376304, d377688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36593 q selected
  have h5 (q : Pattern) (selected : d376305 q = 0) : d377689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376305, d377689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376305, d377689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376306 q = 0) : d377690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376306, d377690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376306, d377690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376428 q = 0) : d377812 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376428, d377812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376428, d377812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376578 q = 0) : d377914 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376578, d377914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376578, d377914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376579 q = 0) : d377915 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376579, d377915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376579, d377915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376580 q = 0) : d377916 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376580, d377916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376580, d377916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39407 (p : Pattern) (selected : d376584 p = 0) : d377920 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376304 q = 0) : d377688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376304, d377688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39358 q selected
    | true =>
      simp only [d376304, d377688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36593 q selected
  have h2 (q : Pattern) (selected : d376305 q = 0) : d377689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376305, d377689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376305, d377689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376306 q = 0) : d377690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376306, d377690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376306, d377690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376578 q = 0) : d377914 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376578, d377914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376578, d377914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376583 q = 0) : d377919 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376583, d377919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376583, d377919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376584 q = 0) : d377920 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376584, d377920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376584, d377920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39408 (p : Pattern) (selected : d376590 p = 0) : d377926 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376581 q = 0) : d377917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39406 q selected
    | true =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376582 q = 0) : d377918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376585 q = 0) : d377921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39407 q selected
    | true =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376586 q = 0) : d377922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376587 q = 0) : d377923 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376587, d377923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376587, d377923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376588 q = 0) : d377924 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376588, d377924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376588, d377924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376589 q = 0) : d377925 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376589, d377925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376589, d377925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376590 q = 0) : d377926 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376590, d377926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376590, d377926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39409 (p : Pattern) (selected : d376594 p = 0) : d377930 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376585 q = 0) : d377921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39407 q selected
    | true =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376586 q = 0) : d377922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376591 q = 0) : d377927 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376591, d377927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376591, d377927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376592 q = 0) : d377928 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376592, d377928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376592, d377928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376593 q = 0) : d377929 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376593, d377929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376593, d377929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376594 q = 0) : d377930 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376594, d377930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376594, d377930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39410 (p : Pattern) (selected : d376600 p = 0) : d377936 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376595 q = 0) : d377931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376595, d377931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39408 q selected
    | true =>
      simp only [d376595, d377931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39409 q selected
  have h2 (q : Pattern) (selected : d376596 q = 0) : d377932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376596, d377932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376596, d377932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376597 q = 0) : d377933 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376597, d377933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376597, d377933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376598 q = 0) : d377934 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376598, d377934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376598, d377934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376599 q = 0) : d377935 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376599, d377935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376599, d377935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376600 q = 0) : d377936 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376600, d377936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376600, d377936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39411 (p : Pattern) (selected : d376603 p = 0) : d377939 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376581 q = 0) : d377917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39406 q selected
    | true =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376582 q = 0) : d377918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376585 q = 0) : d377921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39407 q selected
    | true =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376586 q = 0) : d377922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376587 q = 0) : d377923 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376587, d377923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376587, d377923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376588 q = 0) : d377924 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376588, d377924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376588, d377924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376589 q = 0) : d377925 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376589, d377925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376589, d377925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376603 q = 0) : d377939 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376603, d377939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376603, d377939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39412 (p : Pattern) (selected : d376604 p = 0) : d377940 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376585 q = 0) : d377921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39407 q selected
    | true =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376586 q = 0) : d377922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376591 q = 0) : d377927 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376591, d377927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376591, d377927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376592 q = 0) : d377928 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376592, d377928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376592, d377928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376593 q = 0) : d377929 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376593, d377929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376593, d377929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376604 q = 0) : d377940 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376604, d377940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376604, d377940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39413 (p : Pattern) (selected : d376610 p = 0) : d377946 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376595 q = 0) : d377931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376595, d377931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39408 q selected
    | true =>
      simp only [d376595, d377931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39409 q selected
  have h2 (q : Pattern) (selected : d376596 q = 0) : d377932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376596, d377932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376596, d377932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376597 q = 0) : d377933 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376597, d377933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376597, d377933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376598 q = 0) : d377934 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376598, d377934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376598, d377934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376599 q = 0) : d377935 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376599, d377935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376599, d377935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376605 q = 0) : d377941 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376605, d377941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39411 q selected
    | true =>
      simp only [d376605, d377941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39412 q selected
  have h7 (q : Pattern) (selected : d376606 q = 0) : d377942 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376606, d377942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376606, d377942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376607 q = 0) : d377943 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376607, d377943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376607, d377943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376608 q = 0) : d377944 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376608, d377944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376608, d377944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376609 q = 0) : d377945 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376609, d377945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376609, d377945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d376610 q = 0) : d377946 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376610, d377946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376610, d377946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39414 (p : Pattern) (selected : d376615 p = 0) : d377951 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376581 q = 0) : d377917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39406 q selected
    | true =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376582 q = 0) : d377918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376585 q = 0) : d377921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39407 q selected
    | true =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376586 q = 0) : d377922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376587 q = 0) : d377923 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376587, d377923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376587, d377923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376588 q = 0) : d377924 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376588, d377924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376588, d377924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376614 q = 0) : d377950 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376614, d377950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376614, d377950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376615 q = 0) : d377951 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376615, d377951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376615, d377951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39415 (p : Pattern) (selected : d376617 p = 0) : d377953 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376585 q = 0) : d377921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39407 q selected
    | true =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376586 q = 0) : d377922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376591 q = 0) : d377927 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376591, d377927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376591, d377927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376592 q = 0) : d377928 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376592, d377928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376592, d377928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376616 q = 0) : d377952 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376616, d377952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376616, d377952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376617 q = 0) : d377953 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376617, d377953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376617, d377953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39416 (p : Pattern) (selected : d376624 p = 0) : d377960 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376581 q = 0) : d377917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39406 q selected
    | true =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376582 q = 0) : d377918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376585 q = 0) : d377921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39407 q selected
    | true =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376586 q = 0) : d377922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376587 q = 0) : d377923 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376587, d377923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376587, d377923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376622 q = 0) : d377958 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376622, d377958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376622, d377958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376623 q = 0) : d377959 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376623, d377959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376623, d377959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376624 q = 0) : d377960 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376624, d377960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376624, d377960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39417 (p : Pattern) (selected : d376627 p = 0) : d377963 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376585 q = 0) : d377921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39407 q selected
    | true =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376586 q = 0) : d377922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376591 q = 0) : d377927 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376591, d377927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376591, d377927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376625 q = 0) : d377961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376625, d377961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376625, d377961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376626 q = 0) : d377962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376626, d377962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376626, d377962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376627 q = 0) : d377963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376627, d377963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376627, d377963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39418 (p : Pattern) (selected : d376634 p = 0) : d377970 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376405 q = 0) : d377789 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376405, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39375 q selected
    | true =>
      simp only [d376405, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376406 q = 0) : d377790 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376406, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376406, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376631 q = 0) : d377967 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376631, d377967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376631, d377967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376292 q = 0) : d377676 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376292, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39356 q selected
    | true =>
      simp only [d376292, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376293 q = 0) : d377677 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376293, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376293, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376407 q = 0) : d377791 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376407, d377791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376407, d377791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376632 q = 0) : d377968 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376632, d377968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376632, d377968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376633 q = 0) : d377969 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376633, d377969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376633, d377969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d351904 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36591 q selected
    | true =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d351905 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376294 q = 0) : d377678 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376294, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376294, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d376408 q = 0) : d377792 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376408, d377792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376408, d377792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d376409 q = 0) : d377793 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376409, d377793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376409, d377793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d376634 q = 0) : d377970 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d376634, d377970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376634, d377970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro39419 (p : Pattern) (selected : d376642 p = 0) : d377978 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376405 q = 0) : d377789 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376405, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39375 q selected
    | true =>
      simp only [d376405, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376406 q = 0) : d377790 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376406, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376406, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376292 q = 0) : d377676 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376292, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39356 q selected
    | true =>
      simp only [d376292, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376293 q = 0) : d377677 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376293, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376293, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376407 q = 0) : d377791 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376407, d377791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376407, d377791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351904 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36591 q selected
    | true =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d351905 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376294 q = 0) : d377678 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376294, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376294, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376408 q = 0) : d377792 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376408, d377792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376408, d377792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376409 q = 0) : d377793 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376409, d377793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376409, d377793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376639 q = 0) : d377975 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376639, d377975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376639, d377975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h12 (q : Pattern) (selected : d376640 q = 0) : d377976 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376640, d377976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d376640, d377976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d376641 q = 0) : d377977 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376641, d377977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376641, d377977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d376642 q = 0) : d377978 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d376642, d377978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376642, d377978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro39420 (p : Pattern) (selected : d376651 p = 0) : d377987 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376405 q = 0) : d377789 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376405, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39375 q selected
    | true =>
      simp only [d376405, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376406 q = 0) : d377790 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376406, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376406, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376648 q = 0) : d377984 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376648, d377984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376648, d377984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376649 q = 0) : d377985 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376649, d377985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376649, d377985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376650 q = 0) : d377986 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376650, d377986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376650, d377986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d351904 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36591 q selected
    | true =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d351905 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376639 q = 0) : d377975 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376639, d377975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376639, d377975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376640 q = 0) : d377976 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376640, d377976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376640, d377976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d376641 q = 0) : d377977 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376641, d377977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376641, d377977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376651 q = 0) : d377987 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d376651, d377987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376651, d377987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39421 (p : Pattern) (selected : d376657 p = 0) : d377993 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376635 q = 0) : d377971 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376635, d377971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39418 q selected
    | true =>
      simp only [d376635, d377971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376636 q = 0) : d377972 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376636, d377972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376636, d377972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376637 q = 0) : d377973 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376637, d377973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376637, d377973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376638 q = 0) : d377974 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376638, d377974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376638, d377974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376643 q = 0) : d377979 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376643, d377979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39419 q selected
    | true =>
      simp only [d376643, d377979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376644 q = 0) : d377980 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376644, d377980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376644, d377980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376645 q = 0) : d377981 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376645, d377981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376645, d377981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376646 q = 0) : d377982 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376646, d377982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376646, d377982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376647 q = 0) : d377983 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376647, d377983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376647, d377983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376652 q = 0) : d377988 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376652, d377988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39420 q selected
    | true =>
      simp only [d376652, d377988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376653 q = 0) : d377989 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376653, d377989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376653, d377989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d376654 q = 0) : d377990 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376654, d377990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376654, d377990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d376655 q = 0) : d377991 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376655, d377991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376655, d377991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d376419 q = 0) : d377803 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376419, d377803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39377 q selected
    | true =>
      simp only [d376419, d377803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d376420 q = 0) : d377804 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376420, d377804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d376420, d377804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d376421 q = 0) : d377805 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376421, d377805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376421, d377805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d376422 q = 0) : d377806 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376422, d377806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d376422, d377806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d376656 q = 0) : d377992 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376656, d377992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376656, d377992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d376657 q = 0) : d377993 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376657, d377993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376657, d377993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro39422 (p : Pattern) (selected : d376661 p = 0) : d377997 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376419 q = 0) : d377803 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376419, d377803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39377 q selected
    | true =>
      simp only [d376419, d377803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376420 q = 0) : d377804 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376420, d377804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376420, d377804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376421 q = 0) : d377805 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376421, d377805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376421, d377805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376422 q = 0) : d377806 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376422, d377806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376422, d377806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351910 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
    | true =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d351911 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d351912 q = 0) : d354144 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d351912, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351912, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d351913 q = 0) : d354145 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d351913, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d351913, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376423 q = 0) : d377807 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376423, d377807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376423, d377807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d351914 q = 0) : d354146 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d351914, d354146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d351914, d354146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376661 q = 0) : d377997 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376661, d377997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376661, d377997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39423 (p : Pattern) (selected : d376667 p = 0) : d378003 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376658 q = 0) : d377994 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376658, d377994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39421 q selected
    | true =>
      simp only [d376658, d377994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39378 q selected
  have h2 (q : Pattern) (selected : d376659 q = 0) : d377995 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376659, d377995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376659, d377995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376660 q = 0) : d377996 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376660, d377996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376660, d377996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376662 q = 0) : d377998 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376662, d377998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39378 q selected
    | true =>
      simp only [d376662, d377998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39422 q selected
  have h5 (q : Pattern) (selected : d376663 q = 0) : d377999 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376663, d377999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376663, d377999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376664 q = 0) : d378000 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376664, d378000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376664, d378000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376665 q = 0) : d378001 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376665, d378001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376665, d378001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376425 q = 0) : d377809 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376425, d377809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39378 q selected
    | true =>
      simp only [d376425, d377809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39358 q selected
  have h9 (q : Pattern) (selected : d376426 q = 0) : d377810 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376426, d377810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376426, d377810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376427 q = 0) : d377811 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376427, d377811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376427, d377811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d376304 q = 0) : d377688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376304, d377688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39358 q selected
    | true =>
      simp only [d376304, d377688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36593 q selected
  have h12 (q : Pattern) (selected : d376305 q = 0) : d377689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376305, d377689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376305, d377689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d376306 q = 0) : d377690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376306, d377690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376306, d377690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d376428 q = 0) : d377812 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376428, d377812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376428, d377812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d376666 q = 0) : d378002 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376666, d378002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376666, d378002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d376667 q = 0) : d378003 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376667, d378003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d376667, d378003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro39424 (p : Pattern) (selected : d376673 p = 0) : d378009 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376668 q = 0) : d378004 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376668, d378004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39423 q selected
    | true =>
      simp only [d376668, d378004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376669 q = 0) : d378005 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376669, d378005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376669, d378005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376581 q = 0) : d377917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39406 q selected
    | true =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376582 q = 0) : d377918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376670 q = 0) : d378006 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376670, d378006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376670, d378006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376671 q = 0) : d378007 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376671, d378007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376671, d378007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376672 q = 0) : d378008 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376672, d378008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376672, d378008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376673 q = 0) : d378009 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376673, d378009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376673, d378009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39425 (p : Pattern) (selected : d376675 p = 0) : d377788 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d352041 q = 0) : d253268 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d352041, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352041, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352042 q = 0) : d354133 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d352042, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352042, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376438 q = 0) : d377674 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d376438, d377674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376438, d377674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376675 q = 0) : d377788 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d376675, d377788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376675, d377788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro39426 (p : Pattern) (selected : d376681 p = 0) : d377794 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376676 q = 0) : d377789 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376676, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39425 q selected
    | true =>
      simp only [d376676, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376677 q = 0) : d377790 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376677, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376677, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376440 q = 0) : d377676 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376440, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39381 q selected
    | true =>
      simp only [d376440, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376441 q = 0) : d377677 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376441, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376441, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376678 q = 0) : d377791 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376678, d377791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376678, d377791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352045 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36614 q selected
    | true =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352046 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376442 q = 0) : d377678 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376442, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376442, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376679 q = 0) : d377792 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376679, d377792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376679, d377792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376680 q = 0) : d377793 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376680, d377793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376680, d377793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352047 q = 0) : d354138 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352047, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352047, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d376443 q = 0) : d377679 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376443, d377679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376443, d377679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d376444 q = 0) : d377680 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376444, d377680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376444, d377680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d376681 q = 0) : d377794 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d376681, d377794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376681, d377794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro39427 (p : Pattern) (selected : d376689 p = 0) : d377802 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376440 q = 0) : d377676 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376440, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39381 q selected
    | true =>
      simp only [d376440, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376441 q = 0) : d377677 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376441, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376441, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352045 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36614 q selected
    | true =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352046 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376442 q = 0) : d377678 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376442, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376442, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376687 q = 0) : d377800 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376687, d377800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376687, d377800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376688 q = 0) : d377801 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376688, d377801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376688, d377801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352047 q = 0) : d354138 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352047, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352047, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352048 q = 0) : d354139 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352048, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352048, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d352049 q = 0) : d354140 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352049, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352049, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376689 q = 0) : d377802 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d376689, d377802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376689, d377802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39428 (p : Pattern) (selected : d376695 p = 0) : d377808 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376682 q = 0) : d377795 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376682, d377795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39426 q selected
    | true =>
      simp only [d376682, d377795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376683 q = 0) : d377796 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376683, d377796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376683, d377796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376684 q = 0) : d377797 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376684, d377797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376684, d377797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376685 q = 0) : d377798 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376685, d377798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376685, d377798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376446 q = 0) : d377682 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376446, d377682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39382 q selected
    | true =>
      simp only [d376446, d377682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376447 q = 0) : d377683 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376447, d377683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376447, d377683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376448 q = 0) : d377684 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376448, d377684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376448, d377684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376449 q = 0) : d377685 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376449, d377685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376449, d377685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376686 q = 0) : d377799 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376686, d377799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376686, d377799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376690 q = 0) : d377803 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376690, d377803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39427 q selected
    | true =>
      simp only [d376690, d377803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376691 q = 0) : d377804 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376691, d377804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376691, d377804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d376692 q = 0) : d377805 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376692, d377805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376692, d377805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d376693 q = 0) : d377806 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376693, d377806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376693, d377806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d352051 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36615 q selected
    | true =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d352052 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d352053 q = 0) : d354144 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352053, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352053, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d352054 q = 0) : d354145 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352054, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d352054, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d376694 q = 0) : d377807 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376694, d377807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376694, d377807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d376695 q = 0) : d377808 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376695, d377808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376695, d377808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro39429 (p : Pattern) (selected : d376702 p = 0) : d377916 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376696 q = 0) : d377809 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376696, d377809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39428 q selected
    | true =>
      simp only [d376696, d377809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39383 q selected
  have h2 (q : Pattern) (selected : d376697 q = 0) : d377810 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376697, d377810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376697, d377810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376698 q = 0) : d377811 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376698, d377811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376698, d377811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376452 q = 0) : d377688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376452, d377688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39383 q selected
    | true =>
      simp only [d376452, d377688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36616 q selected
  have h5 (q : Pattern) (selected : d376453 q = 0) : d377689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376453, d377689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376453, d377689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376454 q = 0) : d377690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376454, d377690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376454, d377690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376699 q = 0) : d377812 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376699, d377812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376699, d377812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376700 q = 0) : d377914 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376700, d377914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376700, d377914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376701 q = 0) : d377915 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376701, d377915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376701, d377915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376702 q = 0) : d377916 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376702, d377916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376702, d377916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39430 (p : Pattern) (selected : d376706 p = 0) : d377920 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376452 q = 0) : d377688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376452, d377688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39383 q selected
    | true =>
      simp only [d376452, d377688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36616 q selected
  have h2 (q : Pattern) (selected : d376453 q = 0) : d377689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376453, d377689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376453, d377689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376454 q = 0) : d377690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376454, d377690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376454, d377690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376700 q = 0) : d377914 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376700, d377914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376700, d377914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376705 q = 0) : d377919 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376705, d377919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376705, d377919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376706 q = 0) : d377920 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376706, d377920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376706, d377920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39431 (p : Pattern) (selected : d376712 p = 0) : d377926 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376703 q = 0) : d377917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376703, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39429 q selected
    | true =>
      simp only [d376703, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376704 q = 0) : d377918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376704, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376704, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376707 q = 0) : d377921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376707, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39430 q selected
    | true =>
      simp only [d376707, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376708 q = 0) : d377922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376708, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376708, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376709 q = 0) : d377923 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376709, d377923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376709, d377923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376710 q = 0) : d377924 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376710, d377924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376710, d377924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376711 q = 0) : d377925 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376711, d377925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376711, d377925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376712 q = 0) : d377926 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376712, d377926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376712, d377926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39432 (p : Pattern) (selected : d376716 p = 0) : d377930 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376707 q = 0) : d377921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376707, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39430 q selected
    | true =>
      simp only [d376707, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376708 q = 0) : d377922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376708, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376708, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376713 q = 0) : d377927 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376713, d377927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376713, d377927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376714 q = 0) : d377928 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376714, d377928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376714, d377928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376715 q = 0) : d377929 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376715, d377929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376715, d377929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376716 q = 0) : d377930 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376716, d377930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376716, d377930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39433 (p : Pattern) (selected : d376722 p = 0) : d378015 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376581 q = 0) : d377917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39406 q selected
    | true =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376582 q = 0) : d377918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376719 q = 0) : d378012 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376719, d378012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376719, d378012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376720 q = 0) : d378013 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376720, d378013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376720, d378013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376721 q = 0) : d378014 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376721, d378014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376721, d378014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376722 q = 0) : d378015 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376722, d378015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376722, d378015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39434 (p : Pattern) (selected : d376728 p = 0) : d378021 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376618 q = 0) : d377954 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376618, d377954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39414 q selected
    | true =>
      simp only [d376618, d377954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39415 q selected
  have h2 (q : Pattern) (selected : d376619 q = 0) : d377955 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376619, d377955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376619, d377955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376620 q = 0) : d377956 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376620, d377956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376620, d377956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376621 q = 0) : d377957 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376621, d377957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376621, d377957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376628 q = 0) : d377964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376628, d377964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39416 q selected
    | true =>
      simp only [d376628, d377964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39417 q selected
  have h6 (q : Pattern) (selected : d376629 q = 0) : d377965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376629, d377965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376629, d377965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376630 q = 0) : d377966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376630, d377966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376630, d377966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376674 q = 0) : d378010 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376674, d378010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39424 q selected
    | true =>
      simp only [d376674, d378010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39408 q selected
  have h9 (q : Pattern) (selected : d376717 q = 0) : d377931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376717, d377931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39431 q selected
    | true =>
      simp only [d376717, d377931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39432 q selected
  have h10 (q : Pattern) (selected : d376718 q = 0) : d378011 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376718, d378011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376718, d378011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d376723 q = 0) : d378016 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376723, d378016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39433 q selected
    | true =>
      simp only [d376723, d378016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d376724 q = 0) : d378017 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376724, d378017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d376724, d378017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d376725 q = 0) : d378018 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376725, d378018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376725, d378018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d376726 q = 0) : d378019 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376726, d378019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376726, d378019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d376727 q = 0) : d378020 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376727, d378020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376727, d378020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d376728 q = 0) : d378021 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376728, d378021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376728, d378021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro39435 (p : Pattern) (selected : d376729 p = 0) : d378022 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376581 q = 0) : d377917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39406 q selected
    | true =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376582 q = 0) : d377918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376585 q = 0) : d377921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39407 q selected
    | true =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376586 q = 0) : d377922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376587 q = 0) : d377923 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376587, d377923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376587, d377923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376588 q = 0) : d377924 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376588, d377924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376588, d377924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376614 q = 0) : d377950 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376614, d377950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376614, d377950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376729 q = 0) : d378022 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376729, d378022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376729, d378022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39436 (p : Pattern) (selected : d376730 p = 0) : d378023 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376585 q = 0) : d377921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39407 q selected
    | true =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376586 q = 0) : d377922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376591 q = 0) : d377927 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376591, d377927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376591, d377927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376592 q = 0) : d377928 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376592, d377928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376592, d377928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376616 q = 0) : d377952 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376616, d377952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376616, d377952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376730 q = 0) : d378023 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376730, d378023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376730, d378023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39437 (p : Pattern) (selected : d376735 p = 0) : d378028 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376581 q = 0) : d377917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39406 q selected
    | true =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376582 q = 0) : d377918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376585 q = 0) : d377921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39407 q selected
    | true =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376586 q = 0) : d377922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376587 q = 0) : d377923 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376587, d377923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376587, d377923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376622 q = 0) : d377958 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376622, d377958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376622, d377958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376623 q = 0) : d377959 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376623, d377959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376623, d377959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376735 q = 0) : d378028 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376735, d378028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376735, d378028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39438 (p : Pattern) (selected : d376736 p = 0) : d378029 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376585 q = 0) : d377921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39407 q selected
    | true =>
      simp only [d376585, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376586 q = 0) : d377922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376586, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376591 q = 0) : d377927 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376591, d377927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376591, d377927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376625 q = 0) : d377961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376625, d377961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376625, d377961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376626 q = 0) : d377962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376626, d377962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376626, d377962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376736 q = 0) : d378029 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376736, d378029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376736, d378029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39439 (p : Pattern) (selected : d376740 p = 0) : d378033 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376668 q = 0) : d378004 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376668, d378004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39423 q selected
    | true =>
      simp only [d376668, d378004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376669 q = 0) : d378005 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376669, d378005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376669, d378005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376581 q = 0) : d377917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39406 q selected
    | true =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376582 q = 0) : d377918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376670 q = 0) : d378006 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376670, d378006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376670, d378006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376671 q = 0) : d378007 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376671, d378007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376671, d378007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376672 q = 0) : d378008 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376672, d378008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376672, d378008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376740 q = 0) : d378033 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376740, d378033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376740, d378033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39440 (p : Pattern) (selected : d376742 p = 0) : d377939 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376703 q = 0) : d377917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376703, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39429 q selected
    | true =>
      simp only [d376703, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376704 q = 0) : d377918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376704, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376704, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376707 q = 0) : d377921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376707, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39430 q selected
    | true =>
      simp only [d376707, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376708 q = 0) : d377922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376708, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376708, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376709 q = 0) : d377923 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376709, d377923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376709, d377923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376710 q = 0) : d377924 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376710, d377924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376710, d377924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376711 q = 0) : d377925 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376711, d377925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376711, d377925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376742 q = 0) : d377939 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376742, d377939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376742, d377939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39441 (p : Pattern) (selected : d376743 p = 0) : d377940 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376707 q = 0) : d377921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376707, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39430 q selected
    | true =>
      simp only [d376707, d377921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376708 q = 0) : d377922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376708, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376708, d377922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376713 q = 0) : d377927 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376713, d377927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376713, d377927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376714 q = 0) : d377928 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376714, d377928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376714, d377928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376715 q = 0) : d377929 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376715, d377929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376715, d377929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376743 q = 0) : d377940 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376743, d377940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376743, d377940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39442 (p : Pattern) (selected : d376746 p = 0) : d378036 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376581 q = 0) : d377917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39406 q selected
    | true =>
      simp only [d376581, d377917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376582 q = 0) : d377918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376582, d377918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376719 q = 0) : d378012 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376719, d378012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376719, d378012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376720 q = 0) : d378013 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376720, d378013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376720, d378013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376721 q = 0) : d378014 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376721, d378014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376721, d378014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376746 q = 0) : d378036 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376746, d378036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376746, d378036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39443 (p : Pattern) (selected : d376752 p = 0) : d378042 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376618 q = 0) : d377954 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376618, d377954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39414 q selected
    | true =>
      simp only [d376618, d377954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39415 q selected
  have h2 (q : Pattern) (selected : d376619 q = 0) : d377955 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376619, d377955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376619, d377955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376620 q = 0) : d377956 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376620, d377956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376620, d377956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376621 q = 0) : d377957 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376621, d377957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376621, d377957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376628 q = 0) : d377964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376628, d377964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39416 q selected
    | true =>
      simp only [d376628, d377964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39417 q selected
  have h6 (q : Pattern) (selected : d376629 q = 0) : d377965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376629, d377965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376629, d377965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376630 q = 0) : d377966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376630, d377966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376630, d377966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376674 q = 0) : d378010 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376674, d378010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39424 q selected
    | true =>
      simp only [d376674, d378010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39408 q selected
  have h9 (q : Pattern) (selected : d376717 q = 0) : d377931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376717, d377931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39431 q selected
    | true =>
      simp only [d376717, d377931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39432 q selected
  have h10 (q : Pattern) (selected : d376718 q = 0) : d378011 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376718, d378011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376718, d378011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d376723 q = 0) : d378016 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376723, d378016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39433 q selected
    | true =>
      simp only [d376723, d378016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d376724 q = 0) : d378017 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376724, d378017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d376724, d378017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d376725 q = 0) : d378018 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376725, d378018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376725, d378018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d376726 q = 0) : d378019 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376726, d378019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376726, d378019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d376727 q = 0) : d378020 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376727, d378020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376727, d378020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d376731 q = 0) : d378024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376731, d378024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39435 q selected
    | true =>
      simp only [d376731, d378024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39436 q selected
  have h17 (q : Pattern) (selected : d376732 q = 0) : d378025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376732, d378025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376732, d378025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d376733 q = 0) : d378026 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376733, d378026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d376733, d378026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d376734 q = 0) : d378027 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376734, d378027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376734, d378027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d376737 q = 0) : d378030 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376737, d378030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39437 q selected
    | true =>
      simp only [d376737, d378030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39438 q selected
  have h21 (q : Pattern) (selected : d376738 q = 0) : d378031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376738, d378031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376738, d378031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d376739 q = 0) : d378032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376739, d378032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d376739, d378032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d376741 q = 0) : d378034 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376741, d378034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39439 q selected
    | true =>
      simp only [d376741, d378034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39411 q selected
  have h24 (q : Pattern) (selected : d376744 q = 0) : d377941 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376744, d377941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39440 q selected
    | true =>
      simp only [d376744, d377941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39441 q selected
  have h25 (q : Pattern) (selected : d376745 q = 0) : d378035 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376745, d378035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d376745, d378035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d376747 q = 0) : d378037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376747, d378037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39442 q selected
    | true =>
      simp only [d376747, d378037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d376748 q = 0) : d378038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376748, d378038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d376748, d378038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d376749 q = 0) : d378039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376749, d378039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d376749, d378039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d376750 q = 0) : d378040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376750, d378040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d376750, d378040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d376751 q = 0) : d378041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376751, d378041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d376751, d378041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d376752 q = 0) : d378042 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376752, d378042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d376752, d378042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro39444 (p : Pattern) (selected : d376759 p = 0) : d378049 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376595 q = 0) : d377931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376595, d377931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39408 q selected
    | true =>
      simp only [d376595, d377931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39409 q selected
  have h2 (q : Pattern) (selected : d376596 q = 0) : d377932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376596, d377932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376596, d377932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376597 q = 0) : d377933 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376597, d377933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376597, d377933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376598 q = 0) : d377934 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376598, d377934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376598, d377934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376599 q = 0) : d377935 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376599, d377935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376599, d377935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376754 q = 0) : d378044 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376754, d378044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39409 q selected
    | true =>
      simp only [d376754, d378044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376755 q = 0) : d378045 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376755, d378045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376755, d378045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376756 q = 0) : d378046 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376756, d378046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376756, d378046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376757 q = 0) : d378047 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376757, d378047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376757, d378047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376758 q = 0) : d378048 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376758, d378048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376758, d378048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d376759 q = 0) : d378049 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376759, d378049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376759, d378049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39445 (p : Pattern) (selected : d376765 p = 0) : d378055 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376754 q = 0) : d378044 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376754, d378044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39409 q selected
    | true =>
      simp only [d376754, d378044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376755 q = 0) : d378045 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376755, d378045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376755, d378045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376756 q = 0) : d378046 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376756, d378046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376756, d378046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376757 q = 0) : d378047 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376757, d378047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376757, d378047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376758 q = 0) : d378048 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376758, d378048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376758, d378048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376760 q = 0) : d378050 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376760, d378050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39412 q selected
    | true =>
      simp only [d376760, d378050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376761 q = 0) : d378051 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376761, d378051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376761, d378051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376762 q = 0) : d378052 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376762, d378052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376762, d378052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376763 q = 0) : d378053 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376763, d378053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376763, d378053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376764 q = 0) : d378054 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376764, d378054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376764, d378054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d376765 q = 0) : d378055 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376765, d378055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376765, d378055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39446 (p : Pattern) (selected : d376772 p = 0) : d378062 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376741 q = 0) : d378034 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376741, d378034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39439 q selected
    | true =>
      simp only [d376741, d378034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39411 q selected
  have h2 (q : Pattern) (selected : d376744 q = 0) : d377941 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376744, d377941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39440 q selected
    | true =>
      simp only [d376744, d377941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39441 q selected
  have h3 (q : Pattern) (selected : d376745 q = 0) : d378035 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376745, d378035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376745, d378035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376747 q = 0) : d378037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376747, d378037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39442 q selected
    | true =>
      simp only [d376747, d378037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376748 q = 0) : d378038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376748, d378038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376748, d378038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376749 q = 0) : d378039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376749, d378039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376749, d378039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376770 q = 0) : d378060 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376770, d378060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376770, d378060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376771 q = 0) : d378061 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376771, d378061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376771, d378061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376772 q = 0) : d378062 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376772, d378062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376772, d378062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro39447 (p : Pattern) (selected : d376774 p = 0) : d378064 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376760 q = 0) : d378050 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376760, d378050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39412 q selected
    | true =>
      simp only [d376760, d378050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376761 q = 0) : d378051 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376761, d378051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376761, d378051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376762 q = 0) : d378052 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376762, d378052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376762, d378052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376763 q = 0) : d378053 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376763, d378053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376763, d378053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376764 q = 0) : d378054 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376764, d378054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376764, d378054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376774 q = 0) : d378064 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376774, d378064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376774, d378064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39448 (p : Pattern) (selected : d376794 p = 0) : d378084 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376780 q = 0) : d378070 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376780, d378070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376780, d378070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39418 q selected
  have h2 (q : Pattern) (selected : d376635 q = 0) : d377971 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376635, d377971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39418 q selected
    | true =>
      simp only [d376635, d377971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376781 q = 0) : d378071 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376781, d378071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376781, d378071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376636 q = 0) : d377972 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376636, d377972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376636, d377972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376782 q = 0) : d378072 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376782, d378072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376782, d378072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376783 q = 0) : d378073 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376783, d378073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376783, d378073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376784 q = 0) : d378074 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376784, d378074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376784, d378074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39419 q selected
  have h8 (q : Pattern) (selected : d376643 q = 0) : d377979 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376643, d377979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39419 q selected
    | true =>
      simp only [d376643, d377979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376785 q = 0) : d378075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376785, d378075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376785, d378075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376644 q = 0) : d377980 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376644, d377980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376644, d377980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376786 q = 0) : d378076 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376786, d378076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376786, d378076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d376787 q = 0) : d378077 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376787, d378077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d376787, d378077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d376788 q = 0) : d378078 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376788, d378078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376788, d378078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d376789 q = 0) : d378079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376789, d378079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376789, d378079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39420 q selected
  have h15 (q : Pattern) (selected : d376652 q = 0) : d377988 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376652, d377988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39420 q selected
    | true =>
      simp only [d376652, d377988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d376790 q = 0) : d378080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376790, d378080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d376790, d378080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d376653 q = 0) : d377989 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376653, d377989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d376653, d377989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d376791 q = 0) : d378081 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376791, d378081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d376791, d378081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d376792 q = 0) : d378082 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376792, d378082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d376792, d378082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d376516 q = 0) : d377871 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376516, d377871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376516, d377871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39377 q selected
  have h21 (q : Pattern) (selected : d376419 q = 0) : d377803 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376419, d377803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39377 q selected
    | true =>
      simp only [d376419, d377803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d376517 q = 0) : d377872 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376517, d377872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d376517, d377872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d376420 q = 0) : d377804 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376420, d377804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d376420, d377804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d376518 q = 0) : d377873 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376518, d377873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d376518, d377873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d376519 q = 0) : d377874 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376519, d377874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d376519, d377874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d376793 q = 0) : d378083 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376793, d378083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d376793, d378083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d376794 q = 0) : d378084 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376794, d378084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376794, d378084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro39449 (p : Pattern) (selected : d376798 p = 0) : d378088 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376516 q = 0) : d377871 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376516, d377871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376516, d377871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39377 q selected
  have h2 (q : Pattern) (selected : d376419 q = 0) : d377803 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376419, d377803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39377 q selected
    | true =>
      simp only [d376419, d377803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376517 q = 0) : d377872 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376517, d377872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376517, d377872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376420 q = 0) : d377804 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376420, d377804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376420, d377804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376518 q = 0) : d377873 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376518, d377873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376518, d377873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376519 q = 0) : d377874 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376519, d377874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376519, d377874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d351951 q = 0) : d354183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351951, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351951, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
  have h8 (q : Pattern) (selected : d351910 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
    | true =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d351952 q = 0) : d354184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351952, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d351952, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d351911 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d351953 q = 0) : d354185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d351953, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d351953, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d351954 q = 0) : d354186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d351954, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d351954, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d376520 q = 0) : d377875 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376520, d377875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376520, d377875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d351955 q = 0) : d354187 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d351955, d354187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d351955, d354187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d376798 q = 0) : d378088 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376798, d378088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376798, d378088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro39450 (p : Pattern) (selected : d376804 p = 0) : d378094 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376795 q = 0) : d378085 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376795, d378085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39448 q selected
    | true =>
      simp only [d376795, d378085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39396 q selected
  have h2 (q : Pattern) (selected : d376796 q = 0) : d378086 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376796, d378086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376796, d378086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376797 q = 0) : d378087 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376797, d378087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376797, d378087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376799 q = 0) : d378089 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376799, d378089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39396 q selected
    | true =>
      simp only [d376799, d378089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39449 q selected
  have h5 (q : Pattern) (selected : d376800 q = 0) : d378090 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376800, d378090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376800, d378090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376801 q = 0) : d378091 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376801, d378091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376801, d378091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376802 q = 0) : d378092 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376802, d378092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376802, d378092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376522 q = 0) : d377877 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376522, d377877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39396 q selected
    | true =>
      simp only [d376522, d377877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39365 q selected
  have h9 (q : Pattern) (selected : d376523 q = 0) : d377878 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376523, d377878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376523, d377878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376524 q = 0) : d377879 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376524, d377879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376524, d377879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d376347 q = 0) : d377731 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376347, d377731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39365 q selected
    | true =>
      simp only [d376347, d377731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36600 q selected
  have h12 (q : Pattern) (selected : d376348 q = 0) : d377732 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376348, d377732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376348, d377732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d376349 q = 0) : d377733 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376349, d377733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376349, d377733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d376525 q = 0) : d377880 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376525, d377880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376525, d377880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d376803 q = 0) : d378093 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376803, d378093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376803, d378093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d376804 q = 0) : d378094 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376804, d378094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d376804, d378094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro39451 (p : Pattern) (selected : d376809 p = 0) : d378099 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376522 q = 0) : d377877 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376522, d377877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39396 q selected
    | true =>
      simp only [d376522, d377877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39365 q selected
  have h2 (q : Pattern) (selected : d376523 q = 0) : d377878 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376523, d377878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376523, d377878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376524 q = 0) : d377879 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376524, d377879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376524, d377879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376347 q = 0) : d377731 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376347, d377731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39365 q selected
    | true =>
      simp only [d376347, d377731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36600 q selected
  have h5 (q : Pattern) (selected : d376348 q = 0) : d377732 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376348, d377732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376348, d377732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376349 q = 0) : d377733 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376349, d377733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376349, d377733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376525 q = 0) : d377880 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376525, d377880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376525, d377880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376807 q = 0) : d378097 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376807, d378097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376807, d378097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376808 q = 0) : d378098 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376808, d378098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376808, d378098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376809 q = 0) : d378099 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376809, d378099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376809, d378099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39452 (p : Pattern) (selected : d376815 p = 0) : d378105 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376805 q = 0) : d378095 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376805, d378095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39450 q selected
    | true =>
      simp only [d376805, d378095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376806 q = 0) : d378096 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376806, d378096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376806, d378096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376810 q = 0) : d378100 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376810, d378100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39451 q selected
    | true =>
      simp only [d376810, d378100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376811 q = 0) : d378101 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376811, d378101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376811, d378101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376812 q = 0) : d378102 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376812, d378102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376812, d378102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376813 q = 0) : d378103 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376813, d378103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376813, d378103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376814 q = 0) : d378104 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376814, d378104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376814, d378104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376815 q = 0) : d378105 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376815, d378105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376815, d378105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39453 (p : Pattern) (selected : d376817 p = 0) : d378107 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376347 q = 0) : d377731 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376347, d377731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39365 q selected
    | true =>
      simp only [d376347, d377731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36600 q selected
  have h2 (q : Pattern) (selected : d376348 q = 0) : d377732 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376348, d377732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376348, d377732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376349 q = 0) : d377733 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376349, d377733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376349, d377733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376807 q = 0) : d378097 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376807, d378097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376807, d378097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376816 q = 0) : d378106 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376816, d378106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376816, d378106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376817 q = 0) : d378107 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376817, d378107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376817, d378107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39454 (p : Pattern) (selected : d376823 p = 0) : d378113 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376810 q = 0) : d378100 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376810, d378100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39451 q selected
    | true =>
      simp only [d376810, d378100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376811 q = 0) : d378101 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376811, d378101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376811, d378101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376818 q = 0) : d378108 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376818, d378108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39453 q selected
    | true =>
      simp only [d376818, d378108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376819 q = 0) : d378109 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376819, d378109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376819, d378109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376820 q = 0) : d378110 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376820, d378110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376820, d378110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376821 q = 0) : d378111 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376821, d378111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376821, d378111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376822 q = 0) : d378112 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376822, d378112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376822, d378112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376823 q = 0) : d378113 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376823, d378113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376823, d378113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39455 (p : Pattern) (selected : d376835 p = 0) : d377876 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376825 q = 0) : d377866 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376825, d377866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376825, d377866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39426 q selected
  have h2 (q : Pattern) (selected : d376682 q = 0) : d377795 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376682, d377795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39426 q selected
    | true =>
      simp only [d376682, d377795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376826 q = 0) : d377867 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376826, d377867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376826, d377867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376683 q = 0) : d377796 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376683, d377796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376683, d377796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376827 q = 0) : d377868 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376827, d377868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376827, d377868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376828 q = 0) : d377869 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376828, d377869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376828, d377869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376535 q = 0) : d377725 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376535, d377725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376535, d377725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39382 q selected
  have h8 (q : Pattern) (selected : d376446 q = 0) : d377682 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376446, d377682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39382 q selected
    | true =>
      simp only [d376446, d377682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376536 q = 0) : d377726 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376536, d377726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376536, d377726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376447 q = 0) : d377683 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376447, d377683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376447, d377683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376537 q = 0) : d377727 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376537, d377727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376537, d377727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d376538 q = 0) : d377728 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376538, d377728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d376538, d377728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d376829 q = 0) : d377870 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376829, d377870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376829, d377870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d376830 q = 0) : d377871 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376830, d377871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376830, d377871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39427 q selected
  have h15 (q : Pattern) (selected : d376690 q = 0) : d377803 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376690, d377803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39427 q selected
    | true =>
      simp only [d376690, d377803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d376831 q = 0) : d377872 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376831, d377872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d376831, d377872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d376691 q = 0) : d377804 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376691, d377804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d376691, d377804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d376832 q = 0) : d377873 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376832, d377873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d376832, d377873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d376833 q = 0) : d377874 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376833, d377874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d376833, d377874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d352126 q = 0) : d354183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352126, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352126, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36615 q selected
  have h21 (q : Pattern) (selected : d352051 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36615 q selected
    | true =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d352127 q = 0) : d354184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352127, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d352127, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d352052 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d352128 q = 0) : d354185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352128, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d352128, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d352129 q = 0) : d354186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352129, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d352129, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d376834 q = 0) : d377875 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376834, d377875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d376834, d377875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d376835 q = 0) : d377876 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376835, d377876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376835, d377876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro39456 (p : Pattern) (selected : d376842 p = 0) : d378099 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376836 q = 0) : d377877 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376836, d377877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39455 q selected
    | true =>
      simp only [d376836, d377877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39399 q selected
  have h2 (q : Pattern) (selected : d376837 q = 0) : d377878 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376837, d377878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376837, d377878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376838 q = 0) : d377879 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376838, d377879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376838, d377879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376541 q = 0) : d377731 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376541, d377731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39399 q selected
    | true =>
      simp only [d376541, d377731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36630 q selected
  have h5 (q : Pattern) (selected : d376542 q = 0) : d377732 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376542, d377732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376542, d377732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376543 q = 0) : d377733 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376543, d377733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376543, d377733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376839 q = 0) : d377880 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376839, d377880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376839, d377880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376840 q = 0) : d378097 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376840, d378097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376840, d378097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376841 q = 0) : d378098 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376841, d378098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376841, d378098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376842 q = 0) : d378099 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376842, d378099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376842, d378099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39457 (p : Pattern) (selected : d376846 p = 0) : d378107 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376541 q = 0) : d377731 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376541, d377731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39399 q selected
    | true =>
      simp only [d376541, d377731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36630 q selected
  have h2 (q : Pattern) (selected : d376542 q = 0) : d377732 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376542, d377732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376542, d377732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376543 q = 0) : d377733 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376543, d377733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376543, d377733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376840 q = 0) : d378097 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376840, d378097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376840, d378097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376845 q = 0) : d378106 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376845, d378106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376845, d378106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376846 q = 0) : d378107 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376846, d378107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376846, d378107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39458 (p : Pattern) (selected : d376852 p = 0) : d378113 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376843 q = 0) : d378100 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376843, d378100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39456 q selected
    | true =>
      simp only [d376843, d378100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376844 q = 0) : d378101 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376844, d378101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376844, d378101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376847 q = 0) : d378108 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376847, d378108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39457 q selected
    | true =>
      simp only [d376847, d378108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376848 q = 0) : d378109 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376848, d378109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376848, d378109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376849 q = 0) : d378110 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376849, d378110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376849, d378110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376850 q = 0) : d378111 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376850, d378111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376850, d378111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376851 q = 0) : d378112 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376851, d378112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376851, d378112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376852 q = 0) : d378113 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376852, d378113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376852, d378113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39459 (p : Pattern) (selected : d376856 p = 0) : d378118 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376847 q = 0) : d378108 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376847, d378108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39457 q selected
    | true =>
      simp only [d376847, d378108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376848 q = 0) : d378109 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376848, d378109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376848, d378109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376853 q = 0) : d378115 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376853, d378115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376853, d378115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376854 q = 0) : d378116 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376854, d378116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376854, d378116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376855 q = 0) : d378117 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376855, d378117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376855, d378117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376856 q = 0) : d378118 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376856, d378118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376856, d378118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39460 (p : Pattern) (selected : d376862 p = 0) : d378124 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376810 q = 0) : d378100 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376810, d378100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39451 q selected
    | true =>
      simp only [d376810, d378100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376811 q = 0) : d378101 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376811, d378101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376811, d378101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376859 q = 0) : d378121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376859, d378121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376859, d378121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376860 q = 0) : d378122 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376860, d378122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376860, d378122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376861 q = 0) : d378123 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376861, d378123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376861, d378123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376862 q = 0) : d378124 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376862, d378124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376862, d378124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39461 (p : Pattern) (selected : d376868 p = 0) : d378130 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376824 q = 0) : d378114 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376824, d378114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39452 q selected
    | true =>
      simp only [d376824, d378114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39454 q selected
  have h2 (q : Pattern) (selected : d376857 q = 0) : d378119 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376857, d378119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39458 q selected
    | true =>
      simp only [d376857, d378119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39459 q selected
  have h3 (q : Pattern) (selected : d376858 q = 0) : d378120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376858, d378120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376858, d378120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376863 q = 0) : d378125 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376863, d378125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39460 q selected
    | true =>
      simp only [d376863, d378125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376864 q = 0) : d378126 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376864, d378126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376864, d378126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376865 q = 0) : d378127 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376865, d378127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376865, d378127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376866 q = 0) : d378128 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376866, d378128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376866, d378128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376867 q = 0) : d378129 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376867, d378129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376867, d378129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376868 q = 0) : d378130 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376868, d378130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376868, d378130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro39462 (p : Pattern) (selected : d376873 p = 0) : d378118 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376818 q = 0) : d378108 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376818, d378108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39453 q selected
    | true =>
      simp only [d376818, d378108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376819 q = 0) : d378109 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376819, d378109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376819, d378109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376870 q = 0) : d378115 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376870, d378115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376870, d378115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376871 q = 0) : d378116 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376871, d378116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376871, d378116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376872 q = 0) : d378117 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376872, d378117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376872, d378117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376873 q = 0) : d378118 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376873, d378118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376873, d378118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39463 (p : Pattern) (selected : d376879 p = 0) : d378137 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376874 q = 0) : d378132 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376874, d378132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39462 q selected
    | true =>
      simp only [d376874, d378132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376875 q = 0) : d378133 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376875, d378133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376875, d378133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376876 q = 0) : d378134 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376876, d378134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376876, d378134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376877 q = 0) : d378135 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376877, d378135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376877, d378135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376878 q = 0) : d378136 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376878, d378136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376878, d378136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376879 q = 0) : d378137 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376879, d378137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376879, d378137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39464 (p : Pattern) (selected : d376885 p = 0) : d378143 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376601 q = 0) : d377937 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376601, d377937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376601, d377937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39410 q selected
  have h2 (q : Pattern) (selected : d376602 q = 0) : d377938 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376602, d377938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376602, d377938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376611 q = 0) : d377947 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376611, d377947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39410 q selected
    | true =>
      simp only [d376611, d377947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39413 q selected
  have h4 (q : Pattern) (selected : d376612 q = 0) : d377948 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376612, d377948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376612, d377948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376613 q = 0) : d377949 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376613, d377949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376613, d377949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376753 q = 0) : d378043 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376753, d378043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39434 q selected
    | true =>
      simp only [d376753, d378043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39443 q selected
  have h7 (q : Pattern) (selected : d376766 q = 0) : d378056 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376766, d378056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39444 q selected
    | true =>
      simp only [d376766, d378056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39445 q selected
  have h8 (q : Pattern) (selected : d376767 q = 0) : d378057 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376767, d378057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376767, d378057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376768 q = 0) : d378058 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376768, d378058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376768, d378058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d376769 q = 0) : d378059 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d376769, d378059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376769, d378059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d376773 q = 0) : d378063 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376773, d378063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376773, d378063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39446 q selected
  have h12 (q : Pattern) (selected : d376775 q = 0) : d378065 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376775, d378065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376775, d378065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39447 q selected
  have h13 (q : Pattern) (selected : d376776 q = 0) : d378066 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376776, d378066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d376776, d378066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d376777 q = 0) : d378067 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376777, d378067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376777, d378067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d376778 q = 0) : d378068 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d376778, d378068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d376778, d378068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d376779 q = 0) : d378069 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d376779, d378069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376779, d378069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d376869 q = 0) : d378131 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376869, d378131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376869, d378131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39461 q selected
  have h18 (q : Pattern) (selected : d376880 q = 0) : d378138 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376880, d378138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376880, d378138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39463 q selected
  have h19 (q : Pattern) (selected : d376881 q = 0) : d378139 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376881, d378139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d376881, d378139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d376882 q = 0) : d378140 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376882, d378140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d376882, d378140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d376883 q = 0) : d378141 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d376883, d378141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d376883, d378141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d376884 q = 0) : d378142 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d376884, d378142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d376884, d378142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d376885 q = 0) : d378143 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d376885, d378143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d376885, d378143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro39465 (p : Pattern) (selected : d376891 p = 0) : d378149 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376886 q = 0) : d378144 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d376886, d378144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376886, d378144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39464 q selected
  have h2 (q : Pattern) (selected : d376887 q = 0) : d378145 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d376887, d378145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376887, d378145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376888 q = 0) : d378146 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d376888, d378146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376888, d378146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376889 q = 0) : d378147 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d376889, d378147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376889, d378147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376890 q = 0) : d378148 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d376890, d378148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376890, d378148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376891 q = 0) : d378149 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d376891, d378149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376891, d378149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39466 (p : Pattern) (selected : d376894 p = 0) : d378152 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376292 q = 0) : d377676 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376292, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39356 q selected
    | true =>
      simp only [d376292, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376293 q = 0) : d377677 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376293, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376293, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d351904 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36591 q selected
    | true =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351905 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376294 q = 0) : d377678 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376294, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376294, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351906 q = 0) : d354138 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d351906, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351906, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376295 q = 0) : d377679 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376295, d377679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376295, d377679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376296 q = 0) : d377680 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376296, d377680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376296, d377680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376894 q = 0) : d378152 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d376894, d378152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376894, d378152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro39467 (p : Pattern) (selected : d376900 p = 0) : d378158 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376635 q = 0) : d377971 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376635, d377971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39418 q selected
    | true =>
      simp only [d376635, d377971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376636 q = 0) : d377972 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376636, d377972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376636, d377972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376637 q = 0) : d377973 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376637, d377973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376637, d377973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376638 q = 0) : d377974 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376638, d377974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376638, d377974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376643 q = 0) : d377979 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376643, d377979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39419 q selected
    | true =>
      simp only [d376643, d377979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376644 q = 0) : d377980 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376644, d377980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376644, d377980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376645 q = 0) : d377981 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376645, d377981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376645, d377981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376646 q = 0) : d377982 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376646, d377982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376646, d377982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376647 q = 0) : d377983 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376647, d377983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376647, d377983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376652 q = 0) : d377988 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376652, d377988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39420 q selected
    | true =>
      simp only [d376652, d377988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376653 q = 0) : d377989 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376653, d377989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376653, d377989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d376654 q = 0) : d377990 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376654, d377990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376654, d377990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d376655 q = 0) : d377991 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376655, d377991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376655, d377991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d376895 q = 0) : d378153 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376895, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39466 q selected
    | true =>
      simp only [d376895, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d376896 q = 0) : d378154 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376896, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d376896, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d376897 q = 0) : d378155 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376897, d378155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376897, d378155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d376898 q = 0) : d378156 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376898, d378156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d376898, d378156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d376899 q = 0) : d378157 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376899, d378157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376899, d378157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d376900 q = 0) : d378158 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376900, d378158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376900, d378158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro39468 (p : Pattern) (selected : d376903 p = 0) : d378161 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376411 q = 0) : d377795 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376411, d377795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39376 q selected
    | true =>
      simp only [d376411, d377795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376412 q = 0) : d377796 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376412, d377796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376412, d377796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376413 q = 0) : d377797 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376413, d377797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376413, d377797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376414 q = 0) : d377798 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376414, d377798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376414, d377798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376895 q = 0) : d378153 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376895, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39466 q selected
    | true =>
      simp only [d376895, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376896 q = 0) : d378154 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376896, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376896, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376897 q = 0) : d378155 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376897, d378155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376897, d378155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376898 q = 0) : d378156 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376898, d378156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376898, d378156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376901 q = 0) : d378159 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376901, d378159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376901, d378159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376902 q = 0) : d378160 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376902, d378160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376902, d378160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376903 q = 0) : d378161 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376903, d378161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376903, d378161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39469 (p : Pattern) (selected : d376907 p = 0) : d378165 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376895 q = 0) : d378153 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376895, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39466 q selected
    | true =>
      simp only [d376895, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376896 q = 0) : d378154 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376896, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376896, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376897 q = 0) : d378155 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376897, d378155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376897, d378155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376898 q = 0) : d378156 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376898, d378156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376898, d378156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376902 q = 0) : d378160 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376902, d378160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376902, d378160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376907 q = 0) : d378165 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376907, d378165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376907, d378165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39470 (p : Pattern) (selected : d376914 p = 0) : d378172 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376904 q = 0) : d378162 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376904, d378162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39467 q selected
    | true =>
      simp only [d376904, d378162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39468 q selected
  have h2 (q : Pattern) (selected : d376905 q = 0) : d378163 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376905, d378163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376905, d378163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376906 q = 0) : d378164 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376906, d378164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376906, d378164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376908 q = 0) : d378166 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376908, d378166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39468 q selected
    | true =>
      simp only [d376908, d378166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39469 q selected
  have h5 (q : Pattern) (selected : d376909 q = 0) : d378167 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376909, d378167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376909, d378167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376910 q = 0) : d378168 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376910, d378168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376910, d378168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376911 q = 0) : d378169 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376911, d378169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376911, d378169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376912 q = 0) : d378170 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376912, d378170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376912, d378170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376913 q = 0) : d378171 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376913, d378171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376913, d378171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376914 q = 0) : d378172 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376914, d378172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376914, d378172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39471 (p : Pattern) (selected : d376918 p = 0) : d378176 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376908 q = 0) : d378166 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376908, d378166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39468 q selected
    | true =>
      simp only [d376908, d378166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39469 q selected
  have h2 (q : Pattern) (selected : d376909 q = 0) : d378167 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376909, d378167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376909, d378167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376910 q = 0) : d378168 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376910, d378168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376910, d378168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376912 q = 0) : d378170 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376912, d378170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376912, d378170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376917 q = 0) : d378175 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376917, d378175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376917, d378175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376918 q = 0) : d378176 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376918, d378176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376918, d378176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39472 (p : Pattern) (selected : d376924 p = 0) : d378182 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376915 q = 0) : d378173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376915, d378173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39470 q selected
    | true =>
      simp only [d376915, d378173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376916 q = 0) : d378174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376916, d378174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376916, d378174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376919 q = 0) : d378177 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376919, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39471 q selected
    | true =>
      simp only [d376919, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376920 q = 0) : d378178 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376920, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376920, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376921 q = 0) : d378179 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376921, d378179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376921, d378179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376922 q = 0) : d378180 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376922, d378180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376922, d378180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376923 q = 0) : d378181 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376923, d378181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376923, d378181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376924 q = 0) : d378182 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376924, d378182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376924, d378182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39473 (p : Pattern) (selected : d376928 p = 0) : d378186 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376919 q = 0) : d378177 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376919, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39471 q selected
    | true =>
      simp only [d376919, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376920 q = 0) : d378178 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376920, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376920, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376925 q = 0) : d378183 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376925, d378183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376925, d378183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376926 q = 0) : d378184 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376926, d378184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376926, d378184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376927 q = 0) : d378185 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376927, d378185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376927, d378185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376928 q = 0) : d378186 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376928, d378186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376928, d378186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39474 (p : Pattern) (selected : d376934 p = 0) : d378192 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376929 q = 0) : d378187 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376929, d378187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39472 q selected
    | true =>
      simp only [d376929, d378187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39473 q selected
  have h2 (q : Pattern) (selected : d376930 q = 0) : d378188 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376930, d378188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376930, d378188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376931 q = 0) : d378189 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376931, d378189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376931, d378189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376932 q = 0) : d378190 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376932, d378190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376932, d378190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376933 q = 0) : d378191 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376933, d378191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376933, d378191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376934 q = 0) : d378192 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376934, d378192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376934, d378192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39475 (p : Pattern) (selected : d376937 p = 0) : d378195 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376915 q = 0) : d378173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376915, d378173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39470 q selected
    | true =>
      simp only [d376915, d378173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376916 q = 0) : d378174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376916, d378174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376916, d378174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376919 q = 0) : d378177 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376919, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39471 q selected
    | true =>
      simp only [d376919, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376920 q = 0) : d378178 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376920, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376920, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376921 q = 0) : d378179 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376921, d378179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376921, d378179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376922 q = 0) : d378180 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376922, d378180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376922, d378180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376923 q = 0) : d378181 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376923, d378181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376923, d378181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376937 q = 0) : d378195 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376937, d378195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376937, d378195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39476 (p : Pattern) (selected : d376938 p = 0) : d378196 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376919 q = 0) : d378177 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376919, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39471 q selected
    | true =>
      simp only [d376919, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376920 q = 0) : d378178 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376920, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376920, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376925 q = 0) : d378183 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376925, d378183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376925, d378183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376926 q = 0) : d378184 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376926, d378184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376926, d378184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376927 q = 0) : d378185 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376927, d378185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376927, d378185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376938 q = 0) : d378196 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376938, d378196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376938, d378196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39477 (p : Pattern) (selected : d376944 p = 0) : d378202 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376929 q = 0) : d378187 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376929, d378187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39472 q selected
    | true =>
      simp only [d376929, d378187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39473 q selected
  have h2 (q : Pattern) (selected : d376930 q = 0) : d378188 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376930, d378188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376930, d378188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376931 q = 0) : d378189 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376931, d378189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376931, d378189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376932 q = 0) : d378190 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376932, d378190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376932, d378190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376933 q = 0) : d378191 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376933, d378191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376933, d378191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376939 q = 0) : d378197 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376939, d378197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39475 q selected
    | true =>
      simp only [d376939, d378197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39476 q selected
  have h7 (q : Pattern) (selected : d376940 q = 0) : d378198 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376940, d378198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376940, d378198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376941 q = 0) : d378199 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376941, d378199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376941, d378199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376942 q = 0) : d378200 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376942, d378200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376942, d378200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376943 q = 0) : d378201 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376943, d378201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376943, d378201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d376944 q = 0) : d378202 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376944, d378202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376944, d378202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39478 (p : Pattern) (selected : d376949 p = 0) : d378207 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376915 q = 0) : d378173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376915, d378173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39470 q selected
    | true =>
      simp only [d376915, d378173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376916 q = 0) : d378174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376916, d378174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376916, d378174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376919 q = 0) : d378177 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376919, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39471 q selected
    | true =>
      simp only [d376919, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376920 q = 0) : d378178 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376920, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376920, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376921 q = 0) : d378179 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376921, d378179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376921, d378179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376922 q = 0) : d378180 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376922, d378180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376922, d378180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376948 q = 0) : d378206 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376948, d378206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376948, d378206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376949 q = 0) : d378207 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376949, d378207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376949, d378207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39479 (p : Pattern) (selected : d376951 p = 0) : d378209 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376919 q = 0) : d378177 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376919, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39471 q selected
    | true =>
      simp only [d376919, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376920 q = 0) : d378178 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376920, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376920, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376925 q = 0) : d378183 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376925, d378183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376925, d378183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376926 q = 0) : d378184 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376926, d378184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376926, d378184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376950 q = 0) : d378208 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376950, d378208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376950, d378208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376951 q = 0) : d378209 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376951, d378209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376951, d378209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39480 (p : Pattern) (selected : d376958 p = 0) : d378216 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376915 q = 0) : d378173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376915, d378173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39470 q selected
    | true =>
      simp only [d376915, d378173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376916 q = 0) : d378174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376916, d378174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376916, d378174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376919 q = 0) : d378177 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376919, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39471 q selected
    | true =>
      simp only [d376919, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376920 q = 0) : d378178 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376920, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376920, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376921 q = 0) : d378179 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376921, d378179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376921, d378179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376956 q = 0) : d378214 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376956, d378214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376956, d378214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376957 q = 0) : d378215 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376957, d378215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376957, d378215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376958 q = 0) : d378216 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376958, d378216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376958, d378216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39481 (p : Pattern) (selected : d376961 p = 0) : d378219 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376919 q = 0) : d378177 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376919, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39471 q selected
    | true =>
      simp only [d376919, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376920 q = 0) : d378178 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376920, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376920, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376925 q = 0) : d378183 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376925, d378183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376925, d378183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376959 q = 0) : d378217 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376959, d378217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376959, d378217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376960 q = 0) : d378218 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376960, d378218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376960, d378218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376961 q = 0) : d378219 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376961, d378219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376961, d378219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39482 (p : Pattern) (selected : d376967 p = 0) : d378225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376405 q = 0) : d377789 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376405, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39375 q selected
    | true =>
      simp only [d376405, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376406 q = 0) : d377790 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376406, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376406, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376631 q = 0) : d377967 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376631, d377967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376631, d377967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376965 q = 0) : d378223 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376965, d378223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376965, d378223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376966 q = 0) : d378224 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376966, d378224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376966, d378224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376292 q = 0) : d377676 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376292, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39356 q selected
    | true =>
      simp only [d376292, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376293 q = 0) : d377677 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376293, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376293, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376407 q = 0) : d377791 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376407, d377791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376407, d377791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376632 q = 0) : d377968 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376632, d377968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376632, d377968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376633 q = 0) : d377969 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376633, d377969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376633, d377969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376967 q = 0) : d378225 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d376967, d378225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376967, d378225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39483 (p : Pattern) (selected : d376972 p = 0) : d378230 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376405 q = 0) : d377789 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376405, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39375 q selected
    | true =>
      simp only [d376405, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376406 q = 0) : d377790 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376406, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376406, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376631 q = 0) : d377967 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376631, d377967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376631, d377967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376292 q = 0) : d377676 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376292, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39356 q selected
    | true =>
      simp only [d376292, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376293 q = 0) : d377677 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376293, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376293, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376407 q = 0) : d377791 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376407, d377791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376407, d377791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376632 q = 0) : d377968 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376632, d377968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376632, d377968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376633 q = 0) : d377969 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376633, d377969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376633, d377969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376972 q = 0) : d378230 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d376972, d378230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376972, d378230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro39484 (p : Pattern) (selected : d376979 p = 0) : d378237 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376968 q = 0) : d378226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376968, d378226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39482 q selected
    | true =>
      simp only [d376968, d378226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376969 q = 0) : d378227 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376969, d378227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376969, d378227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376970 q = 0) : d378228 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376970, d378228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376970, d378228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376971 q = 0) : d378229 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376971, d378229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376971, d378229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376973 q = 0) : d378231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376973, d378231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39483 q selected
    | true =>
      simp only [d376973, d378231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376974 q = 0) : d378232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376974, d378232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376974, d378232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376975 q = 0) : d378233 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376975, d378233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376975, d378233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376976 q = 0) : d378234 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376976, d378234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376976, d378234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376977 q = 0) : d378235 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376977, d378235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376977, d378235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376652 q = 0) : d377988 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376652, d377988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39420 q selected
    | true =>
      simp only [d376652, d377988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376653 q = 0) : d377989 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376653, d377989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376653, d377989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d376654 q = 0) : d377990 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376654, d377990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376654, d377990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d376655 q = 0) : d377991 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376655, d377991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376655, d377991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d376978 q = 0) : d378236 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376978, d378236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376978, d378236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d376979 q = 0) : d378237 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376979, d378237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376979, d378237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro39485 (p : Pattern) (selected : d376983 p = 0) : d378241 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376652 q = 0) : d377988 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376652, d377988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39420 q selected
    | true =>
      simp only [d376652, d377988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376653 q = 0) : d377989 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376653, d377989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376653, d377989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376654 q = 0) : d377990 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376654, d377990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376654, d377990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376655 q = 0) : d377991 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376655, d377991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376655, d377991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376895 q = 0) : d378153 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376895, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39466 q selected
    | true =>
      simp only [d376895, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376896 q = 0) : d378154 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376896, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376896, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376897 q = 0) : d378155 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376897, d378155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376897, d378155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376898 q = 0) : d378156 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376898, d378156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376898, d378156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376899 q = 0) : d378157 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376899, d378157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376899, d378157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376902 q = 0) : d378160 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376902, d378160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376902, d378160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376983 q = 0) : d378241 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376983, d378241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376983, d378241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39486 (p : Pattern) (selected : d376989 p = 0) : d378247 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376980 q = 0) : d378238 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376980, d378238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39484 q selected
    | true =>
      simp only [d376980, d378238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39467 q selected
  have h2 (q : Pattern) (selected : d376981 q = 0) : d378239 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376981, d378239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376981, d378239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376982 q = 0) : d378240 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376982, d378240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376982, d378240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376984 q = 0) : d378242 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376984, d378242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39467 q selected
    | true =>
      simp only [d376984, d378242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39485 q selected
  have h5 (q : Pattern) (selected : d376985 q = 0) : d378243 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376985, d378243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376985, d378243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376986 q = 0) : d378244 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376986, d378244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376986, d378244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376987 q = 0) : d378245 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376987, d378245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376987, d378245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376904 q = 0) : d378162 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376904, d378162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39467 q selected
    | true =>
      simp only [d376904, d378162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39468 q selected
  have h9 (q : Pattern) (selected : d376905 q = 0) : d378163 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376905, d378163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376905, d378163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376906 q = 0) : d378164 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376906, d378164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376906, d378164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d376908 q = 0) : d378166 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376908, d378166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39468 q selected
    | true =>
      simp only [d376908, d378166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39469 q selected
  have h12 (q : Pattern) (selected : d376909 q = 0) : d378167 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376909, d378167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376909, d378167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d376910 q = 0) : d378168 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376910, d378168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376910, d378168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d376911 q = 0) : d378169 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376911, d378169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376911, d378169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d376988 q = 0) : d378246 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376988, d378246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376988, d378246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d376989 q = 0) : d378247 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376989, d378247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d376989, d378247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro39487 (p : Pattern) (selected : d376995 p = 0) : d378253 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376990 q = 0) : d378248 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376990, d378248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39486 q selected
    | true =>
      simp only [d376990, d378248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376991 q = 0) : d378249 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376991, d378249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376991, d378249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376915 q = 0) : d378173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376915, d378173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39470 q selected
    | true =>
      simp only [d376915, d378173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376916 q = 0) : d378174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376916, d378174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376916, d378174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376992 q = 0) : d378250 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376992, d378250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376992, d378250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376993 q = 0) : d378251 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376993, d378251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376993, d378251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376994 q = 0) : d378252 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376994, d378252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376994, d378252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376995 q = 0) : d378253 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376995, d378253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376995, d378253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39488 (p : Pattern) (selected : d377000 p = 0) : d377970 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376676 q = 0) : d377789 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376676, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39425 q selected
    | true =>
      simp only [d376676, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376677 q = 0) : d377790 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376677, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376677, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376997 q = 0) : d377967 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376997, d377967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376997, d377967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376440 q = 0) : d377676 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376440, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39381 q selected
    | true =>
      simp only [d376440, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376441 q = 0) : d377677 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376441, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376441, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376678 q = 0) : d377791 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376678, d377791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376678, d377791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376998 q = 0) : d377968 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376998, d377968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376998, d377968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376999 q = 0) : d377969 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376999, d377969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376999, d377969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352045 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36614 q selected
    | true =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d352046 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376442 q = 0) : d377678 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376442, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376442, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d376679 q = 0) : d377792 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376679, d377792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376679, d377792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d376680 q = 0) : d377793 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376680, d377793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376680, d377793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d377000 q = 0) : d377970 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d377000, d377970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377000, d377970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro39489 (p : Pattern) (selected : d377008 p = 0) : d377978 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376676 q = 0) : d377789 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376676, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39425 q selected
    | true =>
      simp only [d376676, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376677 q = 0) : d377790 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376677, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376677, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376440 q = 0) : d377676 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376440, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39381 q selected
    | true =>
      simp only [d376440, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376441 q = 0) : d377677 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376441, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376441, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376678 q = 0) : d377791 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376678, d377791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376678, d377791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352045 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36614 q selected
    | true =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352046 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376442 q = 0) : d377678 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376442, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376442, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376679 q = 0) : d377792 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376679, d377792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376679, d377792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376680 q = 0) : d377793 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376680, d377793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376680, d377793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d377005 q = 0) : d377975 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377005, d377975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377005, d377975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h12 (q : Pattern) (selected : d377006 q = 0) : d377976 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d377006, d377976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d377006, d377976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d377007 q = 0) : d377977 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d377007, d377977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d377007, d377977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d377008 q = 0) : d377978 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d377008, d377978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377008, d377978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro39490 (p : Pattern) (selected : d377017 p = 0) : d377987 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376676 q = 0) : d377789 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376676, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39425 q selected
    | true =>
      simp only [d376676, d377789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376677 q = 0) : d377790 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376677, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376677, d377790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377014 q = 0) : d377984 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377014, d377984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377014, d377984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377015 q = 0) : d377985 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d377015, d377985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377015, d377985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377016 q = 0) : d377986 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d377016, d377986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377016, d377986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352045 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36614 q selected
    | true =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352046 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377005 q = 0) : d377975 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377005, d377975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377005, d377975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d377006 q = 0) : d377976 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d377006, d377976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377006, d377976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d377007 q = 0) : d377977 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d377007, d377977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377007, d377977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d377017 q = 0) : d377987 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d377017, d377987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377017, d377987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39491 (p : Pattern) (selected : d377022 p = 0) : d378152 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376440 q = 0) : d377676 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376440, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39381 q selected
    | true =>
      simp only [d376440, d377676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376441 q = 0) : d377677 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376441, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376441, d377677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352045 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36614 q selected
    | true =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352046 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376442 q = 0) : d377678 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376442, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376442, d377678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352047 q = 0) : d354138 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352047, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352047, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376443 q = 0) : d377679 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376443, d377679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376443, d377679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376444 q = 0) : d377680 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376444, d377680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376444, d377680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377022 q = 0) : d378152 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d377022, d378152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377022, d378152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro39492 (p : Pattern) (selected : d377028 p = 0) : d378158 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377001 q = 0) : d377971 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377001, d377971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39488 q selected
    | true =>
      simp only [d377001, d377971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377002 q = 0) : d377972 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377002, d377972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377002, d377972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377003 q = 0) : d377973 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377003, d377973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377003, d377973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377004 q = 0) : d377974 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377004, d377974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377004, d377974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377009 q = 0) : d377979 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377009, d377979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39489 q selected
    | true =>
      simp only [d377009, d377979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377010 q = 0) : d377980 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377010, d377980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377010, d377980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377011 q = 0) : d377981 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377011, d377981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377011, d377981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377012 q = 0) : d377982 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377012, d377982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377012, d377982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377013 q = 0) : d377983 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377013, d377983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377013, d377983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377018 q = 0) : d377988 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377018, d377988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39490 q selected
    | true =>
      simp only [d377018, d377988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d377019 q = 0) : d377989 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377019, d377989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377019, d377989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d377020 q = 0) : d377990 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377020, d377990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377020, d377990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d377021 q = 0) : d377991 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377021, d377991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d377021, d377991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d377023 q = 0) : d378153 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377023, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39491 q selected
    | true =>
      simp only [d377023, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d377024 q = 0) : d378154 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377024, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d377024, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d377025 q = 0) : d378155 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377025, d378155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377025, d378155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d377026 q = 0) : d378156 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377026, d378156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d377026, d378156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d377027 q = 0) : d378157 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377027, d378157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377027, d378157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d377028 q = 0) : d378158 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377028, d378158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377028, d378158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro39493 (p : Pattern) (selected : d377031 p = 0) : d378161 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376682 q = 0) : d377795 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376682, d377795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39426 q selected
    | true =>
      simp only [d376682, d377795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376683 q = 0) : d377796 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376683, d377796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376683, d377796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376684 q = 0) : d377797 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376684, d377797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376684, d377797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376685 q = 0) : d377798 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376685, d377798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376685, d377798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377023 q = 0) : d378153 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377023, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39491 q selected
    | true =>
      simp only [d377023, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377024 q = 0) : d378154 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377024, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377024, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377025 q = 0) : d378155 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377025, d378155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377025, d378155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377026 q = 0) : d378156 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377026, d378156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377026, d378156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377029 q = 0) : d378159 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377029, d378159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377029, d378159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377030 q = 0) : d378160 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377030, d378160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377030, d378160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d377031 q = 0) : d378161 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377031, d378161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377031, d378161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39494 (p : Pattern) (selected : d377035 p = 0) : d378165 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377023 q = 0) : d378153 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377023, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39491 q selected
    | true =>
      simp only [d377023, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377024 q = 0) : d378154 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377024, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377024, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377025 q = 0) : d378155 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377025, d378155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377025, d378155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377026 q = 0) : d378156 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377026, d378156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377026, d378156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377030 q = 0) : d378160 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377030, d378160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377030, d378160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377035 q = 0) : d378165 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377035, d378165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377035, d378165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39495 (p : Pattern) (selected : d377042 p = 0) : d378172 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377032 q = 0) : d378162 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377032, d378162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39492 q selected
    | true =>
      simp only [d377032, d378162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39493 q selected
  have h2 (q : Pattern) (selected : d377033 q = 0) : d378163 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377033, d378163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377033, d378163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377034 q = 0) : d378164 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377034, d378164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377034, d378164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377036 q = 0) : d378166 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377036, d378166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39493 q selected
    | true =>
      simp only [d377036, d378166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39494 q selected
  have h5 (q : Pattern) (selected : d377037 q = 0) : d378167 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377037, d378167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377037, d378167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377038 q = 0) : d378168 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377038, d378168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377038, d378168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377039 q = 0) : d378169 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377039, d378169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377039, d378169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377040 q = 0) : d378170 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377040, d378170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377040, d378170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377041 q = 0) : d378171 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377041, d378171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377041, d378171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377042 q = 0) : d378172 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377042, d378172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377042, d378172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39496 (p : Pattern) (selected : d377046 p = 0) : d378176 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377036 q = 0) : d378166 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377036, d378166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39493 q selected
    | true =>
      simp only [d377036, d378166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39494 q selected
  have h2 (q : Pattern) (selected : d377037 q = 0) : d378167 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377037, d378167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377037, d378167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377038 q = 0) : d378168 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377038, d378168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377038, d378168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377040 q = 0) : d378170 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377040, d378170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377040, d378170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377045 q = 0) : d378175 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377045, d378175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377045, d378175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377046 q = 0) : d378176 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377046, d378176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377046, d378176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39497 (p : Pattern) (selected : d377052 p = 0) : d378182 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377043 q = 0) : d378173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377043, d378173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39495 q selected
    | true =>
      simp only [d377043, d378173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377044 q = 0) : d378174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377044, d378174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377044, d378174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377047 q = 0) : d378177 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377047, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39496 q selected
    | true =>
      simp only [d377047, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377048 q = 0) : d378178 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377048, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377048, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377049 q = 0) : d378179 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377049, d378179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377049, d378179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377050 q = 0) : d378180 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377050, d378180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377050, d378180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377051 q = 0) : d378181 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377051, d378181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377051, d378181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377052 q = 0) : d378182 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377052, d378182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377052, d378182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39498 (p : Pattern) (selected : d377056 p = 0) : d378186 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377047 q = 0) : d378177 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377047, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39496 q selected
    | true =>
      simp only [d377047, d378177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377048 q = 0) : d378178 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377048, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377048, d378178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377053 q = 0) : d378183 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377053, d378183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377053, d378183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377054 q = 0) : d378184 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377054, d378184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377054, d378184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377055 q = 0) : d378185 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377055, d378185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377055, d378185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377056 q = 0) : d378186 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377056, d378186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377056, d378186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39499 (p : Pattern) (selected : d377062 p = 0) : d378259 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376915 q = 0) : d378173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376915, d378173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39470 q selected
    | true =>
      simp only [d376915, d378173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376916 q = 0) : d378174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376916, d378174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376916, d378174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377059 q = 0) : d378256 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377059, d378256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377059, d378256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377060 q = 0) : d378257 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377060, d378257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377060, d378257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377061 q = 0) : d378258 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377061, d378258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377061, d378258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377062 q = 0) : d378259 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377062, d378259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377062, d378259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
