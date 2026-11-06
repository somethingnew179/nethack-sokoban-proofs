import NetHack.Soko22Hazard87.EqIntroBlocks0151
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro38000 (p : Pattern) (selected : d359079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d271355 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d271356 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d359077 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d359078 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d359079 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d359079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro38001 (p : Pattern) (selected : d359085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
    | true =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359081 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359082 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359083 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359084 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359085 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d359085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38002 (p : Pattern) (selected : d359091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359086 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38001 q selected
    | true =>
      simp only [d359086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359087 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359088 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359089 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359090 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359091 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38003 (p : Pattern) (selected : d359097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359092 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38002 q selected
    | true =>
      simp only [d359092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359093 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359094 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359095 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359096 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359097 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38004 (p : Pattern) (selected : d359103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359098 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38003 q selected
    | true =>
      simp only [d359098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359099 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359100 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359101 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359102 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359103 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38005 (p : Pattern) (selected : d359109 p = 1) : d362939 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359042 q = 1) : d359042 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d359048 q = 1) : d359048 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d359076 q = 1) : d359076 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d359104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38004 q selected
    | true =>
      simp only [d359104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359105 q = 1) : d362935 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359105, d362935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359105, d362935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d358966 q = 1) : d358966 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d359106 q = 1) : d362936 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359106, d362936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359106, d362936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359107 q = 1) : d362937 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359107, d362937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359107, d362937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359108 q = 1) : d362938 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359108, d362938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359108, d362938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359109 q = 1) : d362939 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359109, d362939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359109, d362939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro38006 (p : Pattern) (selected : d359121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359098 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38003 q selected
    | true =>
      simp only [d359098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359099 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359100 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359101 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359102 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359121 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38007 (p : Pattern) (selected : d359127 p = 1) : d362944 p = 1 := by
  have h0 (q : Pattern) (selected : d359042 q = 1) : d359042 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359048 q = 1) : d359048 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d359076 q = 1) : d359076 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d359104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38004 q selected
    | true =>
      simp only [d359104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359105 q = 1) : d362935 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359105, d362935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359105, d362935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d358966 q = 1) : d358966 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d359106 q = 1) : d362936 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359106, d362936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359106, d362936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359107 q = 1) : d362937 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359107, d362937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359107, d362937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359108 q = 1) : d362938 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359108, d362938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359108, d362938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359114 q = 1) : d359114 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d359118 q = 1) : d359118 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d359120 q = 1) : d359120 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d359122 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38006 q selected
    | true =>
      simp only [d359122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d359123 q = 1) : d362940 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359123, d362940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359123, d362940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d358973 q = 1) : d358973 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d359124 q = 1) : d362941 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359124, d362941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d359124, d362941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d359125 q = 1) : d362942 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359125, d362942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359125, d362942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d359126 q = 1) : d362943 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359126, d362943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359126, d362943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d359127 q = 1) : d362944 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359127, d362944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359127, d362944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38008 (p : Pattern) (selected : d359136 p = 1) : d362951 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359120 q = 1) : d359120 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d359122 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38006 q selected
    | true =>
      simp only [d359122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359123 q = 1) : d362940 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359123, d362940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359123, d362940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d358973 q = 1) : d358973 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d359124 q = 1) : d362941 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359124, d362941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359124, d362941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359134 q = 1) : d362949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359134, d362949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359134, d362949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359135 q = 1) : d362950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359135, d362950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359135, d362950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359136 q = 1) : d362951 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359136, d362951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359136, d362951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38009 (p : Pattern) (selected : d359166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359161 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38001 q selected
  have h2 (q : Pattern) (selected : d359086 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38001 q selected
    | true =>
      simp only [d359086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359162 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359087 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359163 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359164 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359165 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359166 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38010 (p : Pattern) (selected : d359172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359167 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38009 q selected
    | true =>
      simp only [d359167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359168 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359169 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359170 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359171 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359172 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38011 (p : Pattern) (selected : d359178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38010 q selected
    | true =>
      simp only [d359173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359175 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359176 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359177 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359178 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38012 (p : Pattern) (selected : d359184 p = 1) : d362961 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359160 q = 1) : d359160 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d359179 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38011 q selected
    | true =>
      simp only [d359179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359180 q = 1) : d362957 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359180, d362957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359180, d362957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359007 q = 1) : d359007 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d359181 q = 1) : d362958 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359181, d362958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359181, d362958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359182 q = 1) : d362959 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359182, d362959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359182, d362959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359183 q = 1) : d362960 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359183, d362960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359183, d362960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359184 q = 1) : d362961 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359184, d362961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359184, d362961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38013 (p : Pattern) (selected : d359190 p = 1) : d362967 p = 1 := by
  have h0 (q : Pattern) (selected : d359036 q = 1) : d359036 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359128 q = 1) : d362945 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359128, d362945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38005 q selected
    | true =>
      simp only [d359128, d362945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38007 q selected
  have h2 (q : Pattern) (selected : d359130 q = 1) : d359130 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d359131 q = 1) : d362946 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359131, d362946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359131, d362946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d359132 q = 1) : d362947 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359132, d362947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359132, d362947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359133 q = 1) : d362948 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359133, d362948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359133, d362948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359137 q = 1) : d362952 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359137, d362952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359137, d362952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38008 q selected
  have h8 (q : Pattern) (selected : d359138 q = 1) : d362953 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359138, d362953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359138, d362953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d359139 q = 1) : d362954 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359139, d362954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359139, d362954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d359140 q = 1) : d362955 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359140, d362955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359140, d362955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d359141 q = 1) : d362956 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d359141, d362956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359141, d362956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d359185 q = 1) : d362962 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359185, d362962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359185, d362962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38012 q selected
  have h13 (q : Pattern) (selected : d359186 q = 1) : d362963 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359186, d362963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359186, d362963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d359187 q = 1) : d362964 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359187, d362964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359187, d362964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d359188 q = 1) : d362965 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359188, d362965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d359188, d362965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d359189 q = 1) : d362966 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d359189, d362966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d359189, d362966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d359190 q = 1) : d362967 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d359190, d362967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359190, d362967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro38014 (p : Pattern) (selected : d359261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d49282 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d49282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d49282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d271355 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d271538 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d271356 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d271356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359259 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359077 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359260 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359078 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d359261 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d359261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro38015 (p : Pattern) (selected : d359267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359262 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38014 q selected
    | true =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359263 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
    | true =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359081 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359264 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359082 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359265 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359266 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359083 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d359084 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359267 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d359267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38016 (p : Pattern) (selected : d359273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359268 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38015 q selected
    | true =>
      simp only [d359268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359269 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359270 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359271 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359086 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38001 q selected
    | true =>
      simp only [d359086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359087 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359088 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359089 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359272 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359090 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359273 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38017 (p : Pattern) (selected : d359279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359274 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38016 q selected
    | true =>
      simp only [d359274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38002 q selected
  have h2 (q : Pattern) (selected : d359275 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359276 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359092 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38002 q selected
    | true =>
      simp only [d359092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359093 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359094 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359277 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359095 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359278 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359279 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38018 (p : Pattern) (selected : d359285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359280 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38017 q selected
    | true =>
      simp only [d359280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359281 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359098 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38003 q selected
    | true =>
      simp only [d359098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359099 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359282 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359283 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359284 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359285 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38019 (p : Pattern) (selected : d359297 p = 1) : d362977 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359216 q = 1) : d359216 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d359222 q = 1) : d359222 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d359258 q = 1) : d359258 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d359286 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38018 q selected
    | true =>
      simp only [d359286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38004 q selected
  have h5 (q : Pattern) (selected : d359287 q = 1) : d362973 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359287, d362973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359287, d362973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359293 q = 1) : d359293 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d359294 q = 1) : d362974 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359294, d362974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359294, d362974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359295 q = 1) : d362975 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359295, d362975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359295, d362975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359296 q = 1) : d362976 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359296, d362976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359296, d362976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359297 q = 1) : d362977 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359297, d362977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359297, d362977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro38020 (p : Pattern) (selected : d359309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359280 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38017 q selected
    | true =>
      simp only [d359280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359281 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359098 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38003 q selected
    | true =>
      simp only [d359098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359099 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359282 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359283 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359284 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359309 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38021 (p : Pattern) (selected : d359318 p = 1) : d362982 p = 1 := by
  have h0 (q : Pattern) (selected : d359216 q = 1) : d359216 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359222 q = 1) : d359222 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d359258 q = 1) : d359258 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d359286 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38018 q selected
    | true =>
      simp only [d359286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38004 q selected
  have h4 (q : Pattern) (selected : d359287 q = 1) : d362973 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359287, d362973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359287, d362973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359293 q = 1) : d359293 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d359294 q = 1) : d362974 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359294, d362974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359294, d362974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359295 q = 1) : d362975 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359295, d362975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359295, d362975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359296 q = 1) : d362976 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359296, d362976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359296, d362976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359302 q = 1) : d359302 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d359306 q = 1) : d359306 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d359308 q = 1) : d359308 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d359310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38020 q selected
    | true =>
      simp only [d359310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38006 q selected
  have h13 (q : Pattern) (selected : d359311 q = 1) : d362978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359311, d362978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359311, d362978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359314 q = 1) : d359314 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d359315 q = 1) : d362979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359315, d362979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359315, d362979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d359316 q = 1) : d362980 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359316, d362980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359316, d362980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d359317 q = 1) : d362981 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359317, d362981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359317, d362981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d359318 q = 1) : d362982 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359318, d362982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359318, d362982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro38022 (p : Pattern) (selected : d359327 p = 1) : d362989 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359308 q = 1) : d359308 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d359310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38020 q selected
    | true =>
      simp only [d359310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38006 q selected
  have h3 (q : Pattern) (selected : d359311 q = 1) : d362978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359311, d362978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359311, d362978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359314 q = 1) : d359314 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d359315 q = 1) : d362979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359315, d362979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359315, d362979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359325 q = 1) : d362987 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359325, d362987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359325, d362987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359326 q = 1) : d362988 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359326, d362988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359326, d362988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359327 q = 1) : d362989 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359327, d362989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359327, d362989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38023 (p : Pattern) (selected : d359364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38015 q selected
  have h2 (q : Pattern) (selected : d359268 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38015 q selected
    | true =>
      simp only [d359268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359269 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359361 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359362 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359161 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38001 q selected
  have h8 (q : Pattern) (selected : d359086 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38001 q selected
    | true =>
      simp only [d359086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359162 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359087 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359163 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d359164 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359363 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359165 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d359364 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38024 (p : Pattern) (selected : d359370 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359365 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38023 q selected
    | true =>
      simp only [d359365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38009 q selected
  have h2 (q : Pattern) (selected : d359366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359167 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38009 q selected
    | true =>
      simp only [d359167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359168 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359169 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359368 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359170 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359369 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359370 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38025 (p : Pattern) (selected : d359376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359371 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38024 q selected
    | true =>
      simp only [d359371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359372 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38010 q selected
    | true =>
      simp only [d359173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359373 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359374 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359375 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359376 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38026 (p : Pattern) (selected : d359388 p = 1) : d362999 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359358 q = 1) : d359358 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d359377 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38025 q selected
    | true =>
      simp only [d359377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38011 q selected
  have h3 (q : Pattern) (selected : d359378 q = 1) : d362995 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359378, d362995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359378, d362995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359384 q = 1) : d359384 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d359385 q = 1) : d362996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359385, d362996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359385, d362996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359386 q = 1) : d362997 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359386, d362997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359386, d362997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359387 q = 1) : d362998 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359387, d362998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359387, d362998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359388 q = 1) : d362999 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359388, d362999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359388, d362999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38027 (p : Pattern) (selected : d359400 p = 1) : d363005 p = 1 := by
  have h0 (q : Pattern) (selected : d359210 q = 1) : d359210 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359319 q = 1) : d362983 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359319, d362983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38019 q selected
    | true =>
      simp only [d359319, d362983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38021 q selected
  have h2 (q : Pattern) (selected : d359321 q = 1) : d359321 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d359322 q = 1) : d362984 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359322, d362984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359322, d362984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d359323 q = 1) : d362985 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359323, d362985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359323, d362985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359324 q = 1) : d362986 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359324, d362986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359324, d362986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359328 q = 1) : d362990 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359328, d362990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359328, d362990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38022 q selected
  have h8 (q : Pattern) (selected : d359330 q = 1) : d359330 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d359331 q = 1) : d362991 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359331, d362991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359331, d362991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359332 q = 1) : d362992 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359332, d362992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359332, d362992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d359333 q = 1) : d362993 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359333, d362993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359333, d362993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d359334 q = 1) : d362994 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d359334, d362994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359334, d362994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d359389 q = 1) : d363000 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359389, d363000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359389, d363000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38026 q selected
  have h14 (q : Pattern) (selected : d359395 q = 1) : d359395 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d359396 q = 1) : d363001 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359396, d363001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359396, d363001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d359397 q = 1) : d363002 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359397, d363002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d359397, d363002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d359398 q = 1) : d363003 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359398, d363003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d359398, d363003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d359399 q = 1) : d363004 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d359399, d363004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d359399, d363004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d359400 q = 1) : d363005 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d359400, d363005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359400, d363005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38028 (p : Pattern) (selected : d359406 p = 1) : d363011 p = 1 := by
  have h0 (q : Pattern) (selected : d359021 q = 1) : d359021 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d359191 q = 1) : d362968 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d359191, d362968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359191, d362968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38013 q selected
  have h3 (q : Pattern) (selected : d359192 q = 1) : d362969 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d359192, d362969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359192, d362969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359193 q = 1) : d362970 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d359193, d362970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359193, d362970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359194 q = 1) : d362971 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d359194, d362971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359194, d362971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359195 q = 1) : d362972 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d359195, d362972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359195, d362972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359401 q = 1) : d363006 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d359401, d363006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359401, d363006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38027 q selected
  have h8 (q : Pattern) (selected : d359402 q = 1) : d363007 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d359402, d363007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359402, d363007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359403 q = 1) : d363008 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d359403, d363008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359403, d363008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359404 q = 1) : d363009 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d359404, d363009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359404, d363009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359405 q = 1) : d363010 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d359405, d363010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359405, d363010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d359406 q = 1) : d363011 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d359406, d363011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359406, d363011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro38029 (p : Pattern) (selected : d359513 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d271355 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d272612 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d272612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d272612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359511 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d49282 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d49282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d49282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d271538 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d271538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h7 (q : Pattern) (selected : d271356 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359259 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359512 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359077 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359260 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d359513 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d359513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro38030 (p : Pattern) (selected : d359519 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359514 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38029 q selected
    | true =>
      simp only [d359514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359515 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359262 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38014 q selected
    | true =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359263 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359516 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
    | true =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359081 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359264 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359517 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359518 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359082 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d359265 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d359266 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d359519 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d359519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro38031 (p : Pattern) (selected : d359527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359262 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38014 q selected
    | true =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359263 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
    | true =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359081 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359264 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359525 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359526 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359082 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359083 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d359084 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359527 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d359527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38032 (p : Pattern) (selected : d359533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359520 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38030 q selected
    | true =>
      simp only [d359520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359521 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359522 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359523 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359268 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38015 q selected
    | true =>
      simp only [d359268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359269 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359270 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359271 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359524 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359528 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38031 q selected
    | true =>
      simp only [d359528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359529 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d359530 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d359531 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d359086 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38001 q selected
    | true =>
      simp only [d359086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d359087 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d359087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d359088 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d359089 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d359089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d359532 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d359533 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38033 (p : Pattern) (selected : d359540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359534 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38032 q selected
    | true =>
      simp only [d359534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38016 q selected
  have h2 (q : Pattern) (selected : d359535 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359536 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359274 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38016 q selected
    | true =>
      simp only [d359274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38002 q selected
  have h5 (q : Pattern) (selected : d359275 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359276 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359537 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359538 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359539 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359540 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38034 (p : Pattern) (selected : d359544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359274 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38016 q selected
    | true =>
      simp only [d359274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38002 q selected
  have h2 (q : Pattern) (selected : d359275 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359276 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359538 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359543 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359544 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38035 (p : Pattern) (selected : d359550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359541 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38033 q selected
    | true =>
      simp only [d359541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359542 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359545 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38034 q selected
    | true =>
      simp only [d359545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359546 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359547 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359548 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359549 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359550 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38036 (p : Pattern) (selected : d359554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359545 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38034 q selected
    | true =>
      simp only [d359545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359546 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359551 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359552 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359553 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359554 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38037 (p : Pattern) (selected : d359566 p = 1) : d363016 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359450 q = 1) : d359450 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d359459 q = 1) : d359459 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d359510 q = 1) : d359510 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d359555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38035 q selected
    | true =>
      simp only [d359555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38036 q selected
  have h5 (q : Pattern) (selected : d359556 q = 1) : d363012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359556, d363012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359556, d363012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359562 q = 1) : d359562 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d359563 q = 1) : d363013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359563, d363013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359563, d363013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359564 q = 1) : d363014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359564, d363014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359564, d363014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359565 q = 1) : d363015 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359565, d363015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359565, d363015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359566 q = 1) : d363016 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359566, d363016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359566, d363016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro38038 (p : Pattern) (selected : d359580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359541 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38033 q selected
    | true =>
      simp only [d359541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359542 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359545 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38034 q selected
    | true =>
      simp only [d359545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359546 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359547 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359548 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359549 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38039 (p : Pattern) (selected : d359581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359545 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38034 q selected
    | true =>
      simp only [d359545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359546 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359551 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359552 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359553 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359581 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38040 (p : Pattern) (selected : d359590 p = 1) : d363021 p = 1 := by
  have h0 (q : Pattern) (selected : d359450 q = 1) : d359450 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359459 q = 1) : d359459 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d359510 q = 1) : d359510 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d359555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38035 q selected
    | true =>
      simp only [d359555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38036 q selected
  have h4 (q : Pattern) (selected : d359556 q = 1) : d363012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359556, d363012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359556, d363012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359562 q = 1) : d359562 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d359563 q = 1) : d363013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359563, d363013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359563, d363013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359564 q = 1) : d363014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359564, d363014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359564, d363014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359565 q = 1) : d363015 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359565, d363015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359565, d363015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359572 q = 1) : d359572 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d359577 q = 1) : d359577 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d359579 q = 1) : d359579 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d359582 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38038 q selected
    | true =>
      simp only [d359582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38039 q selected
  have h13 (q : Pattern) (selected : d359583 q = 1) : d363017 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359583, d363017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359583, d363017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359586 q = 1) : d359586 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d359587 q = 1) : d363018 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359587, d363018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359587, d363018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d359588 q = 1) : d363019 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359588, d363019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359588, d363019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d359589 q = 1) : d363020 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359589, d363020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359589, d363020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d359590 q = 1) : d363021 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359590, d363021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359590, d363021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro38041 (p : Pattern) (selected : d359610 p = 1) : d363028 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359579 q = 1) : d359579 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d359582 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38038 q selected
    | true =>
      simp only [d359582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38039 q selected
  have h3 (q : Pattern) (selected : d359583 q = 1) : d363017 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359583, d363017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359583, d363017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359586 q = 1) : d359586 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d359587 q = 1) : d363018 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359587, d363018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359587, d363018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359608 q = 1) : d363026 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359608, d363026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359608, d363026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359609 q = 1) : d363027 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359609, d363027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359609, d363027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359610 q = 1) : d363028 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359610, d363028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359610, d363028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38042 (p : Pattern) (selected : d359673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359663 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38030 q selected
  have h2 (q : Pattern) (selected : d359520 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38030 q selected
    | true =>
      simp only [d359520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359664 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359521 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359665 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359666 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38015 q selected
  have h8 (q : Pattern) (selected : d359268 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38015 q selected
    | true =>
      simp only [d359268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359269 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359361 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d359362 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359667 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359668 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38031 q selected
  have h15 (q : Pattern) (selected : d359528 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38031 q selected
    | true =>
      simp only [d359528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d359669 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d359669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d359529 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d359529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d359670 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d359670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d359671 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d359671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d359161 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38001 q selected
  have h21 (q : Pattern) (selected : d359086 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38001 q selected
    | true =>
      simp only [d359086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d359162 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d359162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d359087 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d359087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d359163 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d359163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d359164 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d359164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d359672 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d359672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d359673 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro38043 (p : Pattern) (selected : d359680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359674 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38042 q selected
    | true =>
      simp only [d359674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38023 q selected
  have h2 (q : Pattern) (selected : d359675 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359676 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359365 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38023 q selected
    | true =>
      simp only [d359365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38009 q selected
  have h5 (q : Pattern) (selected : d359366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359677 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359678 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359679 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359680 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38044 (p : Pattern) (selected : d359684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359365 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38023 q selected
    | true =>
      simp only [d359365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38009 q selected
  have h2 (q : Pattern) (selected : d359366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359678 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359683 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38045 (p : Pattern) (selected : d359690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359681 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38043 q selected
    | true =>
      simp only [d359681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359682 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359685 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38044 q selected
    | true =>
      simp only [d359685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359686 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359687 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359688 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359689 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359690 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38046 (p : Pattern) (selected : d359694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359685 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38044 q selected
    | true =>
      simp only [d359685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359686 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359691 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359692 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359693 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359694 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38047 (p : Pattern) (selected : d359706 p = 1) : d363038 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359662 q = 1) : d359662 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d359695 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38045 q selected
    | true =>
      simp only [d359695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38046 q selected
  have h3 (q : Pattern) (selected : d359696 q = 1) : d363034 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359696, d363034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359696, d363034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359702 q = 1) : d359702 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d359703 q = 1) : d363035 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359703, d363035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359703, d363035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359704 q = 1) : d363036 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359704, d363036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359704, d363036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359705 q = 1) : d363037 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359705, d363037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359705, d363037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359706 q = 1) : d363038 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359706, d363038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359706, d363038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38048 (p : Pattern) (selected : d359723 p = 1) : d363044 p = 1 := by
  have h0 (q : Pattern) (selected : d359442 q = 1) : d359442 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359591 q = 1) : d363022 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359591, d363022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38037 q selected
    | true =>
      simp only [d359591, d363022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38040 q selected
  have h2 (q : Pattern) (selected : d359604 q = 1) : d359604 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d359605 q = 1) : d363023 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359605, d363023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359605, d363023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d359606 q = 1) : d363024 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359606, d363024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359606, d363024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359607 q = 1) : d363025 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359607, d363025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359607, d363025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359611 q = 1) : d363029 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359611, d363029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359611, d363029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38041 q selected
  have h8 (q : Pattern) (selected : d359613 q = 1) : d359613 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d359614 q = 1) : d363030 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359614, d363030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359614, d363030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359615 q = 1) : d363031 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359615, d363031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359615, d363031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d359616 q = 1) : d363032 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359616, d363032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359616, d363032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d359617 q = 1) : d363033 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d359617, d363033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359617, d363033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d359707 q = 1) : d363039 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359707, d363039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359707, d363039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38047 q selected
  have h14 (q : Pattern) (selected : d359718 q = 1) : d359718 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d359719 q = 1) : d363040 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359719, d363040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359719, d363040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d359720 q = 1) : d363041 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359720, d363041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d359720, d363041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d359721 q = 1) : d363042 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359721, d363042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d359721, d363042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d359722 q = 1) : d363043 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d359722, d363043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d359722, d363043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d359723 q = 1) : d363044 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d359723, d363044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359723, d363044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38049 (p : Pattern) (selected : d359729 p = 1) : d363050 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359724 q = 1) : d363045 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d359724, d363045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359724, d363045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38048 q selected
  have h2 (q : Pattern) (selected : d359725 q = 1) : d363046 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d359725, d363046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359725, d363046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359726 q = 1) : d363047 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d359726, d363047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359726, d363047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359727 q = 1) : d363048 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d359727, d363048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359727, d363048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359728 q = 1) : d363049 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d359728, d363049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359728, d363049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359729 q = 1) : d363050 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d359729, d363050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359729, d363050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38050 (p : Pattern) (selected : d359864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d49282 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d49282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d49282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d271355 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d271538 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d271356 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d271356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359259 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359863 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359864 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d359864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38051 (p : Pattern) (selected : d359871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d271355 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d272612 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d272612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d272612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359511 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d49282 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d49282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d49282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d271538 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d271538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h7 (q : Pattern) (selected : d359868 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359869 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d271356 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d359077 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359870 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d359871 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d359871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro38052 (p : Pattern) (selected : d359877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359865 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38050 q selected
    | true =>
      simp only [d359865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359866 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359514 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38029 q selected
    | true =>
      simp only [d359514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359515 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359867 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359872 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38051 q selected
    | true =>
      simp only [d359872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359873 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359262 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38014 q selected
    | true =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359263 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d359874 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359875 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d359876 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359516 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h14 (q : Pattern) (selected : d359080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
    | true =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d359081 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d359264 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d359517 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d359518 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d359518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d359877 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d359877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38053 (p : Pattern) (selected : d359882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359514 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38029 q selected
    | true =>
      simp only [d359514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359515 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359262 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38014 q selected
    | true =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359263 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359516 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
    | true =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359081 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359264 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359517 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359518 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359525 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d359526 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359882 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d359882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro38054 (p : Pattern) (selected : d359890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359514 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38029 q selected
    | true =>
      simp only [d359514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359515 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359262 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38014 q selected
    | true =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359263 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359516 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359888 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359889 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
    | true =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359081 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d359264 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359525 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d359526 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359890 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d359890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro38055 (p : Pattern) (selected : d359895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359262 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38014 q selected
    | true =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359263 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
    | true =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359081 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359264 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359082 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359265 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359266 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359895 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d359895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro38056 (p : Pattern) (selected : d359901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359878 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38052 q selected
    | true =>
      simp only [d359878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359879 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359880 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359881 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359883 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38053 q selected
    | true =>
      simp only [d359883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359884 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359885 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359886 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359887 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359891 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38054 q selected
    | true =>
      simp only [d359891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359892 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d359893 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d359894 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d359896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38055 q selected
    | true =>
      simp only [d359896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d359897 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d359897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d359898 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d359899 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d359899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d359900 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d359901 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38057 (p : Pattern) (selected : d359904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359520 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38030 q selected
    | true =>
      simp only [d359520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359521 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359522 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359523 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38055 q selected
    | true =>
      simp only [d359896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359897 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359898 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359899 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359902 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359903 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359904 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38058 (p : Pattern) (selected : d359908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38055 q selected
    | true =>
      simp only [d359896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359897 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359898 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359899 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359903 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38059 (p : Pattern) (selected : d359915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359905 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38056 q selected
    | true =>
      simp only [d359905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38057 q selected
  have h2 (q : Pattern) (selected : d359906 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359907 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359909 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38057 q selected
    | true =>
      simp only [d359909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38058 q selected
  have h5 (q : Pattern) (selected : d359910 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359911 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359912 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359913 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359914 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359915 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38060 (p : Pattern) (selected : d359919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359909 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38057 q selected
    | true =>
      simp only [d359909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38058 q selected
  have h2 (q : Pattern) (selected : d359910 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359911 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359913 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359918 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359919 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38061 (p : Pattern) (selected : d359925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359916 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38059 q selected
    | true =>
      simp only [d359916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359917 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359920 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38060 q selected
    | true =>
      simp only [d359920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359921 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359922 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359923 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359924 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359925 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38062 (p : Pattern) (selected : d359929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359920 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38060 q selected
    | true =>
      simp only [d359920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359921 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359926 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359927 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359928 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359929 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38063 (p : Pattern) (selected : d359941 p = 1) : d363056 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359792 q = 1) : d359792 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d359801 q = 1) : d359801 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d359862 q = 1) : d359862 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d359930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38061 q selected
    | true =>
      simp only [d359930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38062 q selected
  have h5 (q : Pattern) (selected : d359931 q = 1) : d363052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359931, d363052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359931, d363052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359937 q = 1) : d359937 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d359938 q = 1) : d363053 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359938, d363053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359938, d363053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359939 q = 1) : d363054 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359939, d363054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359939, d363054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359940 q = 1) : d363055 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359940, d363055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359940, d363055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359941 q = 1) : d363056 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359941, d363056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359941, d363056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro38064 (p : Pattern) (selected : d359955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359916 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38059 q selected
    | true =>
      simp only [d359916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359917 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359920 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38060 q selected
    | true =>
      simp only [d359920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359921 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359922 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359923 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359924 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359955 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38065 (p : Pattern) (selected : d359956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359920 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38060 q selected
    | true =>
      simp only [d359920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359921 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359926 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359927 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359928 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359956 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38066 (p : Pattern) (selected : d359965 p = 1) : d363061 p = 1 := by
  have h0 (q : Pattern) (selected : d359792 q = 1) : d359792 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359801 q = 1) : d359801 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d359862 q = 1) : d359862 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d359930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38061 q selected
    | true =>
      simp only [d359930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38062 q selected
  have h4 (q : Pattern) (selected : d359931 q = 1) : d363052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359931, d363052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359931, d363052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359937 q = 1) : d359937 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d359938 q = 1) : d363053 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359938, d363053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359938, d363053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359939 q = 1) : d363054 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359939, d363054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359939, d363054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359940 q = 1) : d363055 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359940, d363055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359940, d363055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359947 q = 1) : d359947 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d359952 q = 1) : d359952 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d359954 q = 1) : d359954 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d359957 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38064 q selected
    | true =>
      simp only [d359957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38065 q selected
  have h13 (q : Pattern) (selected : d359958 q = 1) : d363057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359958, d363057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359958, d363057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359961 q = 1) : d359961 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d359962 q = 1) : d363058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359962, d363058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359962, d363058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d359963 q = 1) : d363059 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359963, d363059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359963, d363059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d359964 q = 1) : d363060 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359964, d363060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359964, d363060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d359965 q = 1) : d363061 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359965, d363061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359965, d363061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro38067 (p : Pattern) (selected : d359985 p = 1) : d363068 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359954 q = 1) : d359954 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d359957 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38064 q selected
    | true =>
      simp only [d359957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38065 q selected
  have h3 (q : Pattern) (selected : d359958 q = 1) : d363057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359958, d363057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359958, d363057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359961 q = 1) : d359961 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d359962 q = 1) : d363058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359962, d363058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359962, d363058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359983 q = 1) : d363066 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359983, d363066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359983, d363066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359984 q = 1) : d363067 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359984, d363067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359984, d363067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359985 q = 1) : d363068 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359985, d363068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359985, d363068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38068 (p : Pattern) (selected : d360073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360055 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38052 q selected
  have h2 (q : Pattern) (selected : d359878 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38052 q selected
    | true =>
      simp only [d359878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d360056 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359879 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360057 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360058 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360059 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38053 q selected
  have h8 (q : Pattern) (selected : d359883 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38053 q selected
    | true =>
      simp only [d359883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d360060 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359884 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d360061 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d360062 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d360062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d360063 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d360064 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38054 q selected
  have h15 (q : Pattern) (selected : d359891 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38054 q selected
    | true =>
      simp only [d359891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d360065 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d360065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d359892 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d359892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d360066 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d360066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d360067 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d360067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d360068 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38055 q selected
  have h21 (q : Pattern) (selected : d359896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38055 q selected
    | true =>
      simp only [d359896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d360069 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d360069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d359897 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d359897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d360070 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d360070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d360071 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d360071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d360072 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d360072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d360073 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d360073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d360073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro38069 (p : Pattern) (selected : d360076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359663 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38030 q selected
  have h2 (q : Pattern) (selected : d359520 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38030 q selected
    | true =>
      simp only [d359520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359664 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359521 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359665 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359666 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360068 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38055 q selected
  have h8 (q : Pattern) (selected : d359896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38055 q selected
    | true =>
      simp only [d359896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d360069 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359897 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d360070 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d360071 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d360071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d360074 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d360075 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d360075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d360076 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d360076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d360076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38070 (p : Pattern) (selected : d360080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360068 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38055 q selected
  have h2 (q : Pattern) (selected : d359896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38055 q selected
    | true =>
      simp only [d359896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d360069 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359897 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360070 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360071 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360075 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d360080 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d360080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38071 (p : Pattern) (selected : d360087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360077 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d360077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38068 q selected
    | true =>
      simp only [d360077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38069 q selected
  have h2 (q : Pattern) (selected : d360078 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d360078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360079 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d360079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360081 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d360081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38069 q selected
    | true =>
      simp only [d360081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38070 q selected
  have h5 (q : Pattern) (selected : d360082 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d360082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360083 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d360083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d360084 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d360084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d360085 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d360085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d360086 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d360086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d360087 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d360087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38072 (p : Pattern) (selected : d360091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360081 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d360081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38069 q selected
    | true =>
      simp only [d360081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38070 q selected
  have h2 (q : Pattern) (selected : d360082 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d360082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360083 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d360083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360085 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d360085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360090 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d360090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360091 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d360091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38073 (p : Pattern) (selected : d360097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360088 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d360088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38071 q selected
    | true =>
      simp only [d360088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d360089 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d360089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d360092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38072 q selected
    | true =>
      simp only [d360092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d360093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d360093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d360094 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d360094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360095 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d360095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360096 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d360096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d360097 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d360097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38074 (p : Pattern) (selected : d360101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d360092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38072 q selected
    | true =>
      simp only [d360092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d360093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d360093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360098 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d360098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d360099 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d360099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360100 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d360100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360101 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d360101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38075 (p : Pattern) (selected : d360113 p = 1) : d363078 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360054 q = 1) : d360054 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d360102 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d360102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38073 q selected
    | true =>
      simp only [d360102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38074 q selected
  have h3 (q : Pattern) (selected : d360103 q = 1) : d363074 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d360103, d363074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360103, d363074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360109 q = 1) : d360109 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d360110 q = 1) : d363075 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d360110, d363075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360110, d363075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360111 q = 1) : d363076 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d360111, d363076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360111, d363076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d360112 q = 1) : d363077 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d360112, d363077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360112, d363077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d360113 q = 1) : d363078 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d360113, d363078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360113, d363078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38076 (p : Pattern) (selected : d360130 p = 1) : d363084 p = 1 := by
  have h0 (q : Pattern) (selected : d359784 q = 1) : d359784 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d359966 q = 1) : d363062 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359966, d363062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38063 q selected
    | true =>
      simp only [d359966, d363062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38066 q selected
  have h2 (q : Pattern) (selected : d359979 q = 1) : d359979 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d359980 q = 1) : d363063 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359980, d363063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359980, d363063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d359981 q = 1) : d363064 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359981, d363064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359981, d363064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359982 q = 1) : d363065 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359982, d363065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359982, d363065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359986 q = 1) : d363069 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359986, d363069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359986, d363069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38067 q selected
  have h8 (q : Pattern) (selected : d359988 q = 1) : d359988 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d359989 q = 1) : d363070 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359989, d363070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359989, d363070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359990 q = 1) : d363071 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359990, d363071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359990, d363071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d359991 q = 1) : d363072 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359991, d363072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359991, d363072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d359992 q = 1) : d363073 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d359992, d363073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359992, d363073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d360114 q = 1) : d363079 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d360114, d363079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360114, d363079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38075 q selected
  have h14 (q : Pattern) (selected : d360125 q = 1) : d360125 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d360126 q = 1) : d363080 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d360126, d363080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d360126, d363080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d360127 q = 1) : d363081 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d360127, d363081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d360127, d363081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d360128 q = 1) : d363082 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d360128, d363082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d360128, d363082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d360129 q = 1) : d363083 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d360129, d363083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d360129, d363083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d360130 q = 1) : d363084 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d360130, d363084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d360130, d363084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38077 (p : Pattern) (selected : d360136 p = 1) : d363090 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360131 q = 1) : d363085 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d360131, d363085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360131, d363085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38076 q selected
  have h2 (q : Pattern) (selected : d360132 q = 1) : d363086 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d360132, d363086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360132, d363086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360133 q = 1) : d363087 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d360133, d363087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360133, d363087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360134 q = 1) : d363088 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d360134, d363088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360134, d363088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d360135 q = 1) : d363089 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d360135, d363089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360135, d363089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360136 q = 1) : d363090 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d360136, d363090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360136, d363090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38078 (p : Pattern) (selected : d360344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d271355 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d272612 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d272612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d272612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360342 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d360342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360343 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d360343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360344 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d360344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38079 (p : Pattern) (selected : d360349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d49282 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d49282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d49282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d271355 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d271538 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359868 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360348 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d360348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d360349 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d360349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro38080 (p : Pattern) (selected : d360352 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d49282 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d49282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d49282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d271355 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d271538 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359868 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360348 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d360348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d271356 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d271356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359077 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359870 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d360352 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d360352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro38081 (p : Pattern) (selected : d360358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d271355 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d272612 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d272612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d272612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360342 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d360342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360343 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d360343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d271356 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359077 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359078 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d360358 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d360358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38082 (p : Pattern) (selected : d360365 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360345 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38050 q selected
    | true =>
      simp only [d360345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38078 q selected
  have h2 (q : Pattern) (selected : d360346 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d360347 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360350 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38079 q selected
    | true =>
      simp only [d360350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360351 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360353 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38080 q selected
    | true =>
      simp only [d360353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360354 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d360355 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d360356 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d360356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d360357 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d360357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d360359 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38029 q selected
    | true =>
      simp only [d360359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38081 q selected
  have h12 (q : Pattern) (selected : d360360 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d360360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d360361 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359262 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38014 q selected
    | true =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d359263 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d360362 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d360363 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d360363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d360363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d360364 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d360364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d360364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d360365 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d360365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d360365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38083 (p : Pattern) (selected : d360375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d271355 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d272612 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d272612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d272612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359511 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d271356 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360372 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d360372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d360373 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d360373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359077 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d360374 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d360374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d360375 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d360375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro38084 (p : Pattern) (selected : d360376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d271355 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d272612 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d272612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d272612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360342 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d360342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360343 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d360343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360376 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d360376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38085 (p : Pattern) (selected : d360382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d360345 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38050 q selected
    | true =>
      simp only [d360345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38078 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d360346 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360359 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38029 q selected
    | true =>
      simp only [d360359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38081 q selected
  have h4 (q : Pattern) (selected : d360360 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d360361 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359872 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38051 q selected
    | true =>
      simp only [d359872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d359873 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d359262 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38014 q selected
    | true =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d359263 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d359874 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d360370 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d360370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d360371 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d360371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d360371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h13 (q : Pattern) (selected : d360377 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38083 q selected
    | true =>
      simp only [d360377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38084 q selected
  have h14 (q : Pattern) (selected : d360378 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d360378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h15 (q : Pattern) (selected : d360379 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d360379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h16 (q : Pattern) (selected : d360380 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d360380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d360380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h17 (q : Pattern) (selected : d360381 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d360381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d360381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h18 (q : Pattern) (selected : d360382 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d360382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d360382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro38086 (p : Pattern) (selected : d360393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d360345 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38050 q selected
    | true =>
      simp only [d360345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38078 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d360346 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360388 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38083 q selected
    | true =>
      simp only [d360388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d360389 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d360390 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360391 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d360391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d360392 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d360392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d360377 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38083 q selected
    | true =>
      simp only [d360377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38084 q selected
  have h9 (q : Pattern) (selected : d360378 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d360378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d359262 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38014 q selected
    | true =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d359263 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d360379 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d360380 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d360380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d360380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h14 (q : Pattern) (selected : d360381 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d360381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d360381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h15 (q : Pattern) (selected : d360393 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d360393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38087 (p : Pattern) (selected : d360407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d360359 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38029 q selected
    | true =>
      simp only [d360359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38081 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d360360 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359262 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38014 q selected
    | true =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d359263 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d360398 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360399 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d360400 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d360400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d360401 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d360401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d360402 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
  have h10 (q : Pattern) (selected : d360403 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d359080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
    | true =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d359081 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h13 (q : Pattern) (selected : d360404 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d360404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359082 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h15 (q : Pattern) (selected : d360405 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d360405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d360405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d360406 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d360406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d360406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h17 (q : Pattern) (selected : d360407 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d360407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d360407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro38088 (p : Pattern) (selected : d360413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360366 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38082 q selected
    | true =>
      simp only [d360366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d360367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d360368 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360369 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360383 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38085 q selected
    | true =>
      simp only [d360383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360384 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360385 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d360386 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d360387 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d360394 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38086 q selected
    | true =>
      simp only [d360394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d360395 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d360395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d360396 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d360397 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d360397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d360408 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38087 q selected
    | true =>
      simp only [d360408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d360409 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d360409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d360410 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d360411 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d360411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d360412 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d360412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d360413 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d360413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38089 (p : Pattern) (selected : d360419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d360345 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38050 q selected
    | true =>
      simp only [d360345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38078 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d360346 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360359 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38029 q selected
    | true =>
      simp only [d360359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38081 q selected
  have h4 (q : Pattern) (selected : d360360 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d360361 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359872 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38051 q selected
    | true =>
      simp only [d359872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d359873 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d359262 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38014 q selected
    | true =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d359263 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d359874 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d360370 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d360370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d360371 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d360371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d360371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h13 (q : Pattern) (selected : d360414 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38014 q selected
    | true =>
      simp only [d360414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
  have h14 (q : Pattern) (selected : d360415 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d360415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h15 (q : Pattern) (selected : d360416 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d359080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
    | true =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h17 (q : Pattern) (selected : d359081 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h18 (q : Pattern) (selected : d359264 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d360417 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d360417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d360417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d360418 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d360418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d360418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h21 (q : Pattern) (selected : d360419 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d360419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d360419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro38090 (p : Pattern) (selected : d360424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d360359 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38029 q selected
    | true =>
      simp only [d360359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38081 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d360360 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360414 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38014 q selected
    | true =>
      simp only [d360414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
  have h4 (q : Pattern) (selected : d360415 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d360416 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359262 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38014 q selected
    | true =>
      simp only [d359262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d359263 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d359080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
    | true =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d359081 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d359264 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d360417 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d360417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d360418 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d360418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d360418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h13 (q : Pattern) (selected : d360402 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
  have h14 (q : Pattern) (selected : d360403 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d360403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h15 (q : Pattern) (selected : d360404 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d360404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h16 (q : Pattern) (selected : d359082 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h17 (q : Pattern) (selected : d360405 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d360405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d360405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d360406 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d360406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d360406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h19 (q : Pattern) (selected : d360424 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d360424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d360424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38091 (p : Pattern) (selected : d360431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360420 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38089 q selected
    | true =>
      simp only [d360420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d360421 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d360422 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360423 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360425 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38090 q selected
    | true =>
      simp only [d360425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360426 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360427 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d360428 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d360429 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d360408 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38087 q selected
    | true =>
      simp only [d360408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d360409 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d360409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d360410 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d360411 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d360411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d360430 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d360430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d360431 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d360431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38092 (p : Pattern) (selected : d360439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360402 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
  have h2 (q : Pattern) (selected : d360403 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d360436 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
    | true =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359081 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359082 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360437 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d360437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d360438 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d360438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d360439 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d360439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d360439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro38093 (p : Pattern) (selected : d360445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360425 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38090 q selected
    | true =>
      simp only [d360425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d360426 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d360427 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360428 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360435 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360440 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38092 q selected
    | true =>
      simp only [d360440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360441 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d360442 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d360443 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d360443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d360444 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d360445 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d360445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38094 (p : Pattern) (selected : d360452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360432 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d360432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38088 q selected
    | true =>
      simp only [d360432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38091 q selected
  have h2 (q : Pattern) (selected : d360433 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d360433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360434 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d360434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360446 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d360446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38091 q selected
    | true =>
      simp only [d360446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38093 q selected
  have h5 (q : Pattern) (selected : d360447 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d360447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360448 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d360448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d360449 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d360449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d360450 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d360450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d360451 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d360451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d360452 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d360452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38095 (p : Pattern) (selected : d360456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360446 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d360446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38091 q selected
    | true =>
      simp only [d360446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38093 q selected
  have h2 (q : Pattern) (selected : d360447 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d360447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360448 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d360448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360450 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d360450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360455 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d360455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360456 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d360456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38096 (p : Pattern) (selected : d360462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360453 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d360453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38094 q selected
    | true =>
      simp only [d360453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d360454 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d360454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360457 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d360457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38095 q selected
    | true =>
      simp only [d360457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d360458 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d360458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d360459 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d360459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360460 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d360460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360461 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d360461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d360462 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d360462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38097 (p : Pattern) (selected : d360466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360457 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d360457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38095 q selected
    | true =>
      simp only [d360457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d360458 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d360458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360463 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d360463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d360464 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d360464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360465 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d360465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360466 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d360466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38098 (p : Pattern) (selected : d360487 p = 1) : d363097 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360275 q = 1) : d360275 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d360284 q = 1) : d360284 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d360341 q = 1) : d360341 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d360467 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d360467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38096 q selected
    | true =>
      simp only [d360467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38097 q selected
  have h5 (q : Pattern) (selected : d360468 q = 1) : d363093 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d360468, d363093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360468, d363093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360483 q = 1) : d360483 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d360484 q = 1) : d363094 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d360484, d363094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360484, d363094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d360485 q = 1) : d363095 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d360485, d363095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360485, d363095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d360486 q = 1) : d363096 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d360486, d363096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360486, d363096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d360487 q = 1) : d363097 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d360487, d363097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360487, d363097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro38099 (p : Pattern) (selected : d360501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360453 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d360453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38094 q selected
    | true =>
      simp only [d360453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d360454 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d360454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360457 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d360457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38095 q selected
    | true =>
      simp only [d360457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d360458 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d360458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d360459 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d360459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360460 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d360460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360461 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d360461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d360501 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d360501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38100 (p : Pattern) (selected : d360502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360457 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d360457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38095 q selected
    | true =>
      simp only [d360457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d360458 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d360458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360463 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d360463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d360464 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d360464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360465 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d360465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360502 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d360502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38101 (p : Pattern) (selected : d360511 p = 1) : d363102 p = 1 := by
  have h0 (q : Pattern) (selected : d360275 q = 1) : d360275 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360284 q = 1) : d360284 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d360341 q = 1) : d360341 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d360467 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d360467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38096 q selected
    | true =>
      simp only [d360467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38097 q selected
  have h4 (q : Pattern) (selected : d360468 q = 1) : d363093 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d360468, d363093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360468, d363093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d360483 q = 1) : d360483 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d360484 q = 1) : d363094 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d360484, d363094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360484, d363094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d360485 q = 1) : d363095 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d360485, d363095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360485, d363095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d360486 q = 1) : d363096 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d360486, d363096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360486, d363096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d360493 q = 1) : d360493 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d360498 q = 1) : d360498 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d360500 q = 1) : d360500 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d360503 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d360503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38099 q selected
    | true =>
      simp only [d360503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38100 q selected
  have h13 (q : Pattern) (selected : d360504 q = 1) : d363098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d360504, d363098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d360504, d363098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d360507 q = 1) : d360507 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d360508 q = 1) : d363099 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d360508, d363099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d360508, d363099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d360509 q = 1) : d363100 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d360509, d363100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d360509, d363100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d360510 q = 1) : d363101 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d360510, d363101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360510, d363101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d360511 q = 1) : d363102 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d360511, d363102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d360511, d363102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro38102 (p : Pattern) (selected : d360531 p = 1) : d363109 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360500 q = 1) : d360500 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d360503 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d360503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38099 q selected
    | true =>
      simp only [d360503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38100 q selected
  have h3 (q : Pattern) (selected : d360504 q = 1) : d363098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d360504, d363098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360504, d363098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360507 q = 1) : d360507 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d360508 q = 1) : d363099 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d360508, d363099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360508, d363099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360529 q = 1) : d363107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d360529, d363107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360529, d363107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d360530 q = 1) : d363108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d360530, d363108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360530, d363108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d360531 q = 1) : d363109 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d360531, d363109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360531, d363109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38103 (p : Pattern) (selected : d360651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360633 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38082 q selected
  have h2 (q : Pattern) (selected : d360366 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38082 q selected
    | true =>
      simp only [d360366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d360634 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360635 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360636 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360637 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38085 q selected
  have h8 (q : Pattern) (selected : d360383 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38085 q selected
    | true =>
      simp only [d360383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d360638 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d360384 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d360384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d360639 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d360640 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d360640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d360641 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d360642 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38086 q selected
  have h15 (q : Pattern) (selected : d360394 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38086 q selected
    | true =>
      simp only [d360394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d360643 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d360643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d360395 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d360395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d360644 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d360644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d360645 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d360645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d360646 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38087 q selected
  have h21 (q : Pattern) (selected : d360408 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38087 q selected
    | true =>
      simp only [d360408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d360647 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d360647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d360409 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d360409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d360648 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d360648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d360649 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d360649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d360650 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d360650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d360651 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d360651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d360651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro38104 (p : Pattern) (selected : d360662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360652 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38089 q selected
  have h2 (q : Pattern) (selected : d360420 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38089 q selected
    | true =>
      simp only [d360420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d360653 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360421 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360654 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360655 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360656 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38090 q selected
  have h8 (q : Pattern) (selected : d360425 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38090 q selected
    | true =>
      simp only [d360425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d360657 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d360426 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d360426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d360658 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d360659 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d360659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d360660 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d360646 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38087 q selected
  have h15 (q : Pattern) (selected : d360408 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38087 q selected
    | true =>
      simp only [d360408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d360647 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d360647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d360409 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d360409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d360648 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d360648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d360649 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d360649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d360661 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d360661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d360662 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d360662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d360662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro38105 (p : Pattern) (selected : d360672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360656 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38090 q selected
  have h2 (q : Pattern) (selected : d360425 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38090 q selected
    | true =>
      simp only [d360425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d360657 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360426 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360658 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360659 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360666 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d360667 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38092 q selected
  have h9 (q : Pattern) (selected : d360440 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38092 q selected
    | true =>
      simp only [d360440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d360668 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d360668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d360441 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d360669 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d360669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d360670 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d360670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d360671 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d360671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d360672 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d360672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38106 (p : Pattern) (selected : d360679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360663 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d360663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38103 q selected
    | true =>
      simp only [d360663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38104 q selected
  have h2 (q : Pattern) (selected : d360664 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d360664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360665 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d360665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360673 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d360673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38104 q selected
    | true =>
      simp only [d360673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38105 q selected
  have h5 (q : Pattern) (selected : d360674 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d360674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360675 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d360675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d360676 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d360676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d360677 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d360677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d360678 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d360678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d360679 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d360679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38107 (p : Pattern) (selected : d360683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360673 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d360673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38104 q selected
    | true =>
      simp only [d360673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38105 q selected
  have h2 (q : Pattern) (selected : d360674 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d360674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360675 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d360675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360677 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d360677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360682 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d360682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360683 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d360683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38108 (p : Pattern) (selected : d360689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360680 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d360680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38106 q selected
    | true =>
      simp only [d360680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d360681 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d360681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d360684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38107 q selected
    | true =>
      simp only [d360684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d360685 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d360685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d360686 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d360686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360687 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d360687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360688 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d360688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d360689 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d360689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38109 (p : Pattern) (selected : d360693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d360684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38107 q selected
    | true =>
      simp only [d360684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d360685 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d360685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360690 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d360690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d360691 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d360691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360692 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d360692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360693 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d360693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38110 (p : Pattern) (selected : d360714 p = 1) : d363119 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360632 q = 1) : d360632 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d360694 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d360694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38108 q selected
    | true =>
      simp only [d360694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38109 q selected
  have h3 (q : Pattern) (selected : d360695 q = 1) : d363115 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d360695, d363115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360695, d363115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360710 q = 1) : d360710 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d360711 q = 1) : d363116 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d360711, d363116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360711, d363116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360712 q = 1) : d363117 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d360712, d363117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360712, d363117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d360713 q = 1) : d363118 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d360713, d363118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360713, d363118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d360714 q = 1) : d363119 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d360714, d363119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360714, d363119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38111 (p : Pattern) (selected : d360731 p = 1) : d363125 p = 1 := by
  have h0 (q : Pattern) (selected : d360267 q = 1) : d360267 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360512 q = 1) : d363103 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d360512, d363103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38098 q selected
    | true =>
      simp only [d360512, d363103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38101 q selected
  have h2 (q : Pattern) (selected : d360525 q = 1) : d360525 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d360526 q = 1) : d363104 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d360526, d363104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360526, d363104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d360527 q = 1) : d363105 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d360527, d363105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360527, d363105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360528 q = 1) : d363106 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d360528, d363106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360528, d363106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d360532 q = 1) : d363110 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d360532, d363110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360532, d363110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38102 q selected
  have h8 (q : Pattern) (selected : d360534 q = 1) : d360534 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d360535 q = 1) : d363111 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d360535, d363111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360535, d363111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d360536 q = 1) : d363112 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d360536, d363112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360536, d363112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d360537 q = 1) : d363113 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d360537, d363113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d360537, d363113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d360538 q = 1) : d363114 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d360538, d363114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360538, d363114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d360715 q = 1) : d363120 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d360715, d363120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360715, d363120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38110 q selected
  have h14 (q : Pattern) (selected : d360726 q = 1) : d360726 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d360727 q = 1) : d363121 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d360727, d363121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d360727, d363121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d360728 q = 1) : d363122 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d360728, d363122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d360728, d363122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d360729 q = 1) : d363123 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d360729, d363123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d360729, d363123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d360730 q = 1) : d363124 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d360730, d363124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d360730, d363124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d360731 q = 1) : d363125 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d360731, d363125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d360731, d363125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38112 (p : Pattern) (selected : d360737 p = 1) : d363131 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360732 q = 1) : d363126 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d360732, d363126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360732, d363126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38111 q selected
  have h2 (q : Pattern) (selected : d360733 q = 1) : d363127 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d360733, d363127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360733, d363127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360734 q = 1) : d363128 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d360734, d363128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360734, d363128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360735 q = 1) : d363129 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d360735, d363129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360735, d363129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d360736 q = 1) : d363130 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d360736, d363130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360736, d363130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360737 q = 1) : d363131 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d360737, d363131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360737, d363131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38113 (p : Pattern) (selected : d360856 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d271355 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d272612 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d272612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d272612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359511 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d360855 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d360855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360856 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d360856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38114 (p : Pattern) (selected : d360863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360857 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38113 q selected
  have h2 (q : Pattern) (selected : d360858 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38084 q selected
  have h3 (q : Pattern) (selected : d360859 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360860 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360861 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d360861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360862 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d360862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360863 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d360863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro38115 (p : Pattern) (selected : d360870 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d271355 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d271355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d271356 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d360372 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d360372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d360869 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d360869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360870 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d360870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38116 (p : Pattern) (selected : d360879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360857 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38113 q selected
  have h2 (q : Pattern) (selected : d360858 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38084 q selected
  have h3 (q : Pattern) (selected : d360859 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360860 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360861 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d360861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360862 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d360862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38115 q selected
  have h8 (q : Pattern) (selected : d360402 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
  have h9 (q : Pattern) (selected : d360872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d360873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d360874 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38115 q selected
    | true =>
      simp only [d360874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d359080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
    | true =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d360875 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d360875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d360876 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d360876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d360877 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d360877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d360877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d360878 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d360878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d360878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d360879 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d360879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro38117 (p : Pattern) (selected : d360885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38114 q selected
    | true =>
      simp only [d360864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d360865 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d360866 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360867 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360868 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360880 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38116 q selected
    | true =>
      simp only [d360880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360881 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d360882 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d360883 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d360883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d360884 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d360885 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d360885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38118 (p : Pattern) (selected : d360887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38114 q selected
    | true =>
      simp only [d360864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d360865 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d360866 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360867 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360880 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38116 q selected
    | true =>
      simp only [d360880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360881 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360882 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d360883 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d360884 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d360886 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d360886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d360887 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d360887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38119 (p : Pattern) (selected : d360891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38115 q selected
  have h2 (q : Pattern) (selected : d360402 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
  have h3 (q : Pattern) (selected : d360872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360874 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d360874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38115 q selected
    | true =>
      simp only [d360874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38000 q selected
    | true =>
      simp only [d359080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360875 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d360875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d360876 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d360876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d360877 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d360877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d360878 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d360878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d360891 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d360891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d360891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h11 p selected
theorem eqIntro38120 (p : Pattern) (selected : d360897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360880 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38116 q selected
    | true =>
      simp only [d360880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d360881 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d360882 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360883 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360886 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360892 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38119 q selected
    | true =>
      simp only [d360892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360893 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d360894 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d360894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d360895 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d360895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d360895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d360896 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d360896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d360897 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d360897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38121 (p : Pattern) (selected : d360904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360888 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d360888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38117 q selected
    | true =>
      simp only [d360888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38118 q selected
  have h2 (q : Pattern) (selected : d360889 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d360889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360890 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d360890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360898 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d360898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38118 q selected
    | true =>
      simp only [d360898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38120 q selected
  have h5 (q : Pattern) (selected : d360899 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d360899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360900 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d360900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d360901 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d360901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d360902 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d360902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d360903 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d360903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d360904 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d360904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38122 (p : Pattern) (selected : d360908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360898 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d360898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38118 q selected
    | true =>
      simp only [d360898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38120 q selected
  have h2 (q : Pattern) (selected : d360899 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d360899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360900 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d360900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360902 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d360902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360907 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d360907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360908 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d360908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38123 (p : Pattern) (selected : d360914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360905 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d360905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38121 q selected
    | true =>
      simp only [d360905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d360906 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d360906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360909 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d360909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38122 q selected
    | true =>
      simp only [d360909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d360910 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d360910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d360911 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d360911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360912 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d360912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360913 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d360913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d360914 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d360914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38124 (p : Pattern) (selected : d360918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360909 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d360909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38122 q selected
    | true =>
      simp only [d360909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d360910 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d360910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360915 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d360915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d360916 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d360916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360917 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d360917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360918 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d360918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38125 (p : Pattern) (selected : d360946 p = 1) : d363139 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360831 q = 1) : d360831 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d360840 q = 1) : d360840 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d360854 q = 1) : d360854 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d360919 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d360919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38123 q selected
    | true =>
      simp only [d360919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38124 q selected
  have h5 (q : Pattern) (selected : d360920 q = 1) : d363135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d360920, d363135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360920, d363135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360942 q = 1) : d360942 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d360943 q = 1) : d363136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d360943, d363136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360943, d363136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d360944 q = 1) : d363137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d360944, d363137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360944, d363137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d360945 q = 1) : d363138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d360945, d363138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360945, d363138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d360946 q = 1) : d363139 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d360946, d363139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360946, d363139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro38126 (p : Pattern) (selected : d360960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360905 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d360905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38121 q selected
    | true =>
      simp only [d360905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d360906 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d360906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360909 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d360909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38122 q selected
    | true =>
      simp only [d360909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d360910 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d360910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d360911 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d360911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360912 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d360912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d360913 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d360913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d360960 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d360960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38127 (p : Pattern) (selected : d360961 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360909 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d360909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38122 q selected
    | true =>
      simp only [d360909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d360910 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d360910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d360915 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d360915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d360916 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d360916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d360917 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d360917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d360961 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d360961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d360961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38128 (p : Pattern) (selected : d360970 p = 1) : d363144 p = 1 := by
  have h0 (q : Pattern) (selected : d360831 q = 1) : d360831 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360840 q = 1) : d360840 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d360854 q = 1) : d360854 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d360919 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d360919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38123 q selected
    | true =>
      simp only [d360919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38124 q selected
  have h4 (q : Pattern) (selected : d360920 q = 1) : d363135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d360920, d363135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360920, d363135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d360942 q = 1) : d360942 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d360943 q = 1) : d363136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d360943, d363136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360943, d363136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d360944 q = 1) : d363137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d360944, d363137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360944, d363137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d360945 q = 1) : d363138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d360945, d363138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360945, d363138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d360952 q = 1) : d360952 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d360957 q = 1) : d360957 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d360959 q = 1) : d360959 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d360962 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d360962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38126 q selected
    | true =>
      simp only [d360962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38127 q selected
  have h13 (q : Pattern) (selected : d360963 q = 1) : d363140 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d360963, d363140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d360963, d363140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d360966 q = 1) : d360966 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d360967 q = 1) : d363141 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d360967, d363141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d360967, d363141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d360968 q = 1) : d363142 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d360968, d363142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d360968, d363142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d360969 q = 1) : d363143 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d360969, d363143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360969, d363143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d360970 q = 1) : d363144 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d360970, d363144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d360970, d363144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro38129 (p : Pattern) (selected : d360990 p = 1) : d363151 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360959 q = 1) : d360959 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d360962 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d360962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38126 q selected
    | true =>
      simp only [d360962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38127 q selected
  have h3 (q : Pattern) (selected : d360963 q = 1) : d363140 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d360963, d363140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360963, d363140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360966 q = 1) : d360966 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d360967 q = 1) : d363141 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d360967, d363141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360967, d363141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360988 q = 1) : d363149 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d360988, d363149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360988, d363149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d360989 q = 1) : d363150 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d360989, d363150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360989, d363150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d360990 q = 1) : d363151 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d360990, d363151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360990, d363151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38130 (p : Pattern) (selected : d361061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d361051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38114 q selected
  have h2 (q : Pattern) (selected : d360864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38114 q selected
    | true =>
      simp only [d360864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d361052 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d361052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360865 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d361053 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d361053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d361054 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d361054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d361055 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d361056 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38116 q selected
  have h9 (q : Pattern) (selected : d360880 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38116 q selected
    | true =>
      simp only [d360880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d361057 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d361057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d360881 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d361058 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d361058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d361059 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d361059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d361060 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d361060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d361061 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d361061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d361061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38131 (p : Pattern) (selected : d361063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d361051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38114 q selected
  have h2 (q : Pattern) (selected : d360864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38114 q selected
    | true =>
      simp only [d360864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d361052 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d361052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360865 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d361053 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d361053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d361054 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d361054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d361056 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38116 q selected
  have h8 (q : Pattern) (selected : d360880 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38116 q selected
    | true =>
      simp only [d360880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d361057 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d361057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d360881 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d360881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d361058 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d361058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d361059 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d361059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d361060 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d361060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d361062 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d361062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d361063 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d361063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d361063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38132 (p : Pattern) (selected : d361072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d361056 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38116 q selected
  have h2 (q : Pattern) (selected : d360880 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38116 q selected
    | true =>
      simp only [d360880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d361057 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d361057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360881 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d360881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d361058 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d361058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d361059 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d361059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d361062 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d361062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d361067 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38119 q selected
  have h9 (q : Pattern) (selected : d360892 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d360892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38119 q selected
    | true =>
      simp only [d360892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d361068 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d361068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d360893 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d360893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d361069 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d361069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d361070 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d361070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d361071 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d361071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d361072 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d361072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d361072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38133 (p : Pattern) (selected : d361079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d361064 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38130 q selected
    | true =>
      simp only [d361064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38131 q selected
  have h2 (q : Pattern) (selected : d361065 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d361066 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d361073 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38131 q selected
    | true =>
      simp only [d361073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38132 q selected
  have h5 (q : Pattern) (selected : d361074 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d361075 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d361076 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d361076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d361077 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d361077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d361078 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d361078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d361078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d361079 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d361079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d361079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38134 (p : Pattern) (selected : d361083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d361073 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38131 q selected
    | true =>
      simp only [d361073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38132 q selected
  have h2 (q : Pattern) (selected : d361074 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d361075 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d361077 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d361077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d361082 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d361082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d361082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d361083 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d361083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d361083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38135 (p : Pattern) (selected : d361089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d361080 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38133 q selected
    | true =>
      simp only [d361080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d361081 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d361084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38134 q selected
    | true =>
      simp only [d361084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d361085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d361086 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d361086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d361087 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d361087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d361088 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d361088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d361089 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d361089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38136 (p : Pattern) (selected : d361093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d361084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38134 q selected
    | true =>
      simp only [d361084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d361085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d361090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d361090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d361091 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d361091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d361092 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d361092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d361093 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d361093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38137 (p : Pattern) (selected : d361120 p = 1) : d363161 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d361050 q = 1) : d361050 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d361094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38135 q selected
    | true =>
      simp only [d361094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38136 q selected
  have h3 (q : Pattern) (selected : d361095 q = 1) : d363157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361095, d363157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d361095, d363157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d361116 q = 1) : d361116 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d361117 q = 1) : d363158 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361117, d363158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d361117, d363158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d361118 q = 1) : d363159 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361118, d363159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361118, d363159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d361119 q = 1) : d363160 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361119, d363160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361119, d363160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d361120 q = 1) : d363161 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361120, d363161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361120, d363161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38138 (p : Pattern) (selected : d361137 p = 1) : d363167 p = 1 := by
  have h0 (q : Pattern) (selected : d360823 q = 1) : d360823 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d360971 q = 1) : d363145 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d360971, d363145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38125 q selected
    | true =>
      simp only [d360971, d363145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38128 q selected
  have h2 (q : Pattern) (selected : d360984 q = 1) : d360984 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d360985 q = 1) : d363146 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d360985, d363146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360985, d363146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d360986 q = 1) : d363147 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d360986, d363147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360986, d363147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360987 q = 1) : d363148 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d360987, d363148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360987, d363148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d360991 q = 1) : d363152 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d360991, d363152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d360991, d363152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38129 q selected
  have h8 (q : Pattern) (selected : d360993 q = 1) : d360993 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d360994 q = 1) : d363153 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d360994, d363153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d360994, d363153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d360995 q = 1) : d363154 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d360995, d363154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d360995, d363154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d360996 q = 1) : d363155 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d360996, d363155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d360996, d363155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d360997 q = 1) : d363156 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d360997, d363156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d360997, d363156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d361121 q = 1) : d363162 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361121, d363162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d361121, d363162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38137 q selected
  have h14 (q : Pattern) (selected : d361132 q = 1) : d361132 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d361133 q = 1) : d363163 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361133, d363163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d361133, d363163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d361134 q = 1) : d363164 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361134, d363164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d361134, d363164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d361135 q = 1) : d363165 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361135, d363165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d361135, d363165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d361136 q = 1) : d363166 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d361136, d363166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d361136, d363166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d361137 q = 1) : d363167 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d361137, d363167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d361137, d363167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38139 (p : Pattern) (selected : d361143 p = 1) : d363173 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d361138 q = 1) : d363168 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d361138, d363168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361138, d363168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38138 q selected
  have h2 (q : Pattern) (selected : d361139 q = 1) : d363169 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d361139, d363169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361139, d363169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d361140 q = 1) : d363170 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d361140, d363170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361140, d363170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d361141 q = 1) : d363171 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d361141, d363171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361141, d363171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d361142 q = 1) : d363172 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d361142, d363172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361142, d363172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d361143 q = 1) : d363173 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d361143, d363173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d361143, d363173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38140 (p : Pattern) (selected : d361148 p = 1) : d363178 p = 1 := by
  have h0 (q : Pattern) (selected : d359730 q = 1) : d363051 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d359730, d363051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38028 q selected
    | true =>
      simp only [d359730, d363051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38049 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d360137 q = 1) : d363091 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d360137, d363091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360137, d363091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38077 q selected
  have h3 (q : Pattern) (selected : d360138 q = 1) : d363092 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d360138, d363092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360138, d363092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360738 q = 1) : d363132 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d360738, d363132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360738, d363132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38112 q selected
  have h5 (q : Pattern) (selected : d360739 q = 1) : d363133 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d360739, d363133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360739, d363133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360740 q = 1) : d363134 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d360740, d363134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360740, d363134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d361144 q = 1) : d363174 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d361144, d363174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d361144, d363174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38139 q selected
  have h8 (q : Pattern) (selected : d361145 q = 1) : d363175 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d361145, d363175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d361145, d363175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d361146 q = 1) : d363176 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d361146, d363176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d361146, d363176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d361147 q = 1) : d363177 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d361147, d363177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d361147, d363177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d361148 q = 1) : d363178 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d361148, d363178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d361148, d363178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h11 p selected
theorem eqIntro38141 (p : Pattern) (selected : d361154 p = 1) : d363184 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d361149 q = 1) : d363179 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d361149, d363179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38140 q selected
    | true =>
      simp only [d361149, d363179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d361150 q = 1) : d363180 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d361150, d363180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d361150, d363180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d361151 q = 1) : d363181 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d361151, d363181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d361151, d363181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d361152 q = 1) : d363182 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d361152, d363182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d361152, d363182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d361153 q = 1) : d363183 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d361153, d363183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d361153, d363183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d361154 q = 1) : d363184 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d361154, d363184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d361154, d363184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38142 (p : Pattern) (selected : d361160 p = 1) : d363190 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d361155 q = 1) : d363185 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d361155, d363185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38141 q selected
    | true =>
      simp only [d361155, d363185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d361156 q = 1) : d363186 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d361156, d363186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d361156, d363186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d361157 q = 1) : d363187 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d361157, d363187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d361157, d363187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d361158 q = 1) : d363188 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d361158, d363188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d361158, d363188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d361159 q = 1) : d363189 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d361159, d363189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d361159, d363189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d361160 q = 1) : d363190 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d361160, d363190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d361160, d363190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38143 (p : Pattern) (selected : d361166 p = 1) : d363196 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d361161 q = 1) : d363191 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d361161, d363191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38142 q selected
    | true =>
      simp only [d361161, d363191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d361162 q = 1) : d363192 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d361162, d363192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d361162, d363192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d361163 q = 1) : d363193 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d361163, d363193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d361163, d363193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d361164 q = 1) : d363194 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d361164, d363194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d361164, d363194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d361165 q = 1) : d363195 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d361165, d363195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d361165, d363195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d361166 q = 1) : d363196 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d361166, d363196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d361166, d363196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38144 (p : Pattern) (selected : d361172 p = 1) : d363202 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d361167 q = 1) : d363197 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d361167, d363197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38143 q selected
    | true =>
      simp only [d361167, d363197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d361168 q = 1) : d363198 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d361168, d363198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d361168, d363198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d361169 q = 1) : d363199 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d361169, d363199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d361169, d363199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d361170 q = 1) : d363200 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d361170, d363200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d361170, d363200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d361171 q = 1) : d363201 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d361171, d363201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d361171, d363201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d361172 q = 1) : d363202 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d361172, d363202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d361172, d363202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38145 (p : Pattern) (selected : d361178 p = 1) : d363208 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d361173 q = 1) : d363203 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d361173, d363203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38144 q selected
    | true =>
      simp only [d361173, d363203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d361174 q = 1) : d363204 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d361174, d363204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d361174, d363204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d361175 q = 1) : d363205 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d361175, d363205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d361175, d363205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d361176 q = 1) : d363206 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d361176, d363206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d361176, d363206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d361177 q = 1) : d363207 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d361177, d363207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d361177, d363207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d361178 q = 1) : d363208 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d361178, d363208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d361178, d363208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38146 (p : Pattern) (selected : d361184 p = 1) : d363214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d361179 q = 1) : d363209 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d361179, d363209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38145 q selected
    | true =>
      simp only [d361179, d363209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d361180 q = 1) : d363210 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d361180, d363210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d361180, d363210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d361181 q = 1) : d363211 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d361181, d363211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d361181, d363211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d361182 q = 1) : d363212 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d361182, d363212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d361182, d363212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d361183 q = 1) : d363213 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d361183, d363213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d361183, d363213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d361184 q = 1) : d363214 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d361184, d363214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d361184, d363214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38147 (p : Pattern) (selected : d361190 p = 1) : d363220 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d361185 q = 1) : d363215 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d361185, d363215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38146 q selected
    | true =>
      simp only [d361185, d363215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d361186 q = 1) : d363216 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d361186, d363216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d361186, d363216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d361187 q = 1) : d363217 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d361187, d363217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d361187, d363217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d361188 q = 1) : d363218 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d361188, d363218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d361188, d363218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d361189 q = 1) : d363219 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d361189, d363219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d361189, d363219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d361190 q = 1) : d363220 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d361190, d363220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d361190, d363220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38148 (p : Pattern) (selected : d363237 p = 0) : d363281 p = 1 := by
  have h0 (q : Pattern) (selected : d359730 q = 0) : d361805 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d359730, d361805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37677 q selected
    | true =>
      simp only [d359730, d361805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37739 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d360137 q = 0) : d362094 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d360137, d362094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360137, d362094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37816 q selected
  have h3 (q : Pattern) (selected : d360138 q = 0) : d362095 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d360138, d362095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360138, d362095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360738 q = 0) : d362505 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d360738, d362505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360738, d362505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37912 q selected
  have h5 (q : Pattern) (selected : d360739 q = 0) : d362506 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d360739, d362506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360739, d362506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360740 q = 0) : d362507 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d360740, d362507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360740, d362507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d363236 q = 0) : d363280 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d363236, d363280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d363236, d363280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d363237 q = 0) : d363281 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d363237, d363281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d363237, d363281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro38149 (p : Pattern) (selected : d363243 p = 0) : d363287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d363238 q = 0) : d363282 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d363238, d363282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38148 q selected
    | true =>
      simp only [d363238, d363282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363239 q = 0) : d363283 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d363239, d363283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363239, d363283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363240 q = 0) : d363284 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d363240, d363284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363240, d363284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363241 q = 0) : d363285 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d363241, d363285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363241, d363285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363242 q = 0) : d363286 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d363242, d363286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363242, d363286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363243 q = 0) : d363287 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d363243, d363287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363243, d363287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38150 (p : Pattern) (selected : d363249 p = 0) : d363293 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d363244 q = 0) : d363288 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d363244, d363288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38149 q selected
    | true =>
      simp only [d363244, d363288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363245 q = 0) : d363289 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d363245, d363289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363245, d363289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363246 q = 0) : d363290 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d363246, d363290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363246, d363290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363247 q = 0) : d363291 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d363247, d363291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363247, d363291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363248 q = 0) : d363292 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d363248, d363292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363248, d363292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363249 q = 0) : d363293 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d363249, d363293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363249, d363293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38151 (p : Pattern) (selected : d363255 p = 0) : d363299 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d363250 q = 0) : d363294 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d363250, d363294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38150 q selected
    | true =>
      simp only [d363250, d363294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363251 q = 0) : d363295 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d363251, d363295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363251, d363295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363252 q = 0) : d363296 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d363252, d363296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363252, d363296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363253 q = 0) : d363297 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d363253, d363297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363253, d363297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363254 q = 0) : d363298 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d363254, d363298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363254, d363298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363255 q = 0) : d363299 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d363255, d363299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363255, d363299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38152 (p : Pattern) (selected : d363261 p = 0) : d363305 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d363256 q = 0) : d363300 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d363256, d363300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38151 q selected
    | true =>
      simp only [d363256, d363300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363257 q = 0) : d363301 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d363257, d363301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363257, d363301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363258 q = 0) : d363302 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d363258, d363302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363258, d363302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363259 q = 0) : d363303 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d363259, d363303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363259, d363303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363260 q = 0) : d363304 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d363260, d363304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363260, d363304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363261 q = 0) : d363305 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d363261, d363305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363261, d363305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38153 (p : Pattern) (selected : d363267 p = 0) : d363311 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d363262 q = 0) : d363306 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d363262, d363306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38152 q selected
    | true =>
      simp only [d363262, d363306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363263 q = 0) : d363307 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d363263, d363307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363263, d363307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363264 q = 0) : d363308 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d363264, d363308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363264, d363308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363265 q = 0) : d363309 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d363265, d363309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363265, d363309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363266 q = 0) : d363310 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d363266, d363310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363266, d363310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363267 q = 0) : d363311 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d363267, d363311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363267, d363311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38154 (p : Pattern) (selected : d363273 p = 0) : d363317 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d363268 q = 0) : d363312 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d363268, d363312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38153 q selected
    | true =>
      simp only [d363268, d363312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363269 q = 0) : d363313 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d363269, d363313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363269, d363313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363270 q = 0) : d363314 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d363270, d363314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363270, d363314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363271 q = 0) : d363315 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d363271, d363315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363271, d363315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363272 q = 0) : d363316 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d363272, d363316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363272, d363316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363273 q = 0) : d363317 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d363273, d363317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363273, d363317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38155 (p : Pattern) (selected : d363279 p = 0) : d363323 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d363274 q = 0) : d363318 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d363274, d363318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38154 q selected
    | true =>
      simp only [d363274, d363318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363275 q = 0) : d363319 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d363275, d363319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363275, d363319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363276 q = 0) : d363320 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d363276, d363320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363276, d363320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363277 q = 0) : d363321 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d363277, d363321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363277, d363321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363278 q = 0) : d363322 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d363278, d363322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363278, d363322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363279 q = 0) : d363323 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d363279, d363323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363279, d363323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38156 (p : Pattern) (selected : d363237 p = 1) : d363757 p = 1 := by
  have h0 (q : Pattern) (selected : d359730 q = 1) : d363051 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d359730, d363051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38028 q selected
    | true =>
      simp only [d359730, d363051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38049 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d360137 q = 1) : d363091 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d360137, d363091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360137, d363091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38077 q selected
  have h3 (q : Pattern) (selected : d360138 q = 1) : d363092 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d360138, d363092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360138, d363092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d360738 q = 1) : d363132 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d360738, d363132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360738, d363132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38112 q selected
  have h5 (q : Pattern) (selected : d360739 q = 1) : d363133 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d360739, d363133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360739, d363133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d360740 q = 1) : d363134 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d360740, d363134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d360740, d363134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d363236 q = 1) : d363756 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d363236, d363756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d363236, d363756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d363237 q = 1) : d363757 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d363237, d363757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d363237, d363757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro38157 (p : Pattern) (selected : d363243 p = 1) : d363763 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d363238 q = 1) : d363758 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d363238, d363758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38156 q selected
    | true =>
      simp only [d363238, d363758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363239 q = 1) : d363759 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d363239, d363759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363239, d363759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363240 q = 1) : d363760 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d363240, d363760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363240, d363760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363241 q = 1) : d363761 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d363241, d363761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363241, d363761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363242 q = 1) : d363762 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d363242, d363762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363242, d363762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363243 q = 1) : d363763 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d363243, d363763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363243, d363763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38158 (p : Pattern) (selected : d363249 p = 1) : d363769 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d363244 q = 1) : d363764 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d363244, d363764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38157 q selected
    | true =>
      simp only [d363244, d363764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363245 q = 1) : d363765 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d363245, d363765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363245, d363765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363246 q = 1) : d363766 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d363246, d363766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363246, d363766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363247 q = 1) : d363767 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d363247, d363767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363247, d363767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363248 q = 1) : d363768 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d363248, d363768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363248, d363768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363249 q = 1) : d363769 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d363249, d363769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363249, d363769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38159 (p : Pattern) (selected : d363255 p = 1) : d363775 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d363250 q = 1) : d363770 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d363250, d363770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38158 q selected
    | true =>
      simp only [d363250, d363770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363251 q = 1) : d363771 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d363251, d363771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363251, d363771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363252 q = 1) : d363772 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d363252, d363772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363252, d363772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363253 q = 1) : d363773 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d363253, d363773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363253, d363773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363254 q = 1) : d363774 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d363254, d363774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363254, d363774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363255 q = 1) : d363775 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d363255, d363775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363255, d363775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38160 (p : Pattern) (selected : d363261 p = 1) : d363781 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d363256 q = 1) : d363776 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d363256, d363776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38159 q selected
    | true =>
      simp only [d363256, d363776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363257 q = 1) : d363777 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d363257, d363777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363257, d363777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363258 q = 1) : d363778 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d363258, d363778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363258, d363778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363259 q = 1) : d363779 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d363259, d363779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363259, d363779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363260 q = 1) : d363780 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d363260, d363780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363260, d363780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363261 q = 1) : d363781 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d363261, d363781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363261, d363781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38161 (p : Pattern) (selected : d363267 p = 1) : d363787 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d363262 q = 1) : d363782 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d363262, d363782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38160 q selected
    | true =>
      simp only [d363262, d363782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363263 q = 1) : d363783 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d363263, d363783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363263, d363783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363264 q = 1) : d363784 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d363264, d363784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363264, d363784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363265 q = 1) : d363785 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d363265, d363785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363265, d363785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363266 q = 1) : d363786 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d363266, d363786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363266, d363786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363267 q = 1) : d363787 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d363267, d363787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363267, d363787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38162 (p : Pattern) (selected : d363273 p = 1) : d363793 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d363268 q = 1) : d363788 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d363268, d363788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38161 q selected
    | true =>
      simp only [d363268, d363788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363269 q = 1) : d363789 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d363269, d363789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363269, d363789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363270 q = 1) : d363790 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d363270, d363790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363270, d363790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363271 q = 1) : d363791 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d363271, d363791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363271, d363791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363272 q = 1) : d363792 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d363272, d363792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363272, d363792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363273 q = 1) : d363793 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d363273, d363793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363273, d363793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38163 (p : Pattern) (selected : d363279 p = 1) : d363799 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d363274 q = 1) : d363794 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d363274, d363794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38162 q selected
    | true =>
      simp only [d363274, d363794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363275 q = 1) : d363795 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d363275, d363795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363275, d363795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363276 q = 1) : d363796 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d363276, d363796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363276, d363796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363277 q = 1) : d363797 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d363277, d363797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363277, d363797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363278 q = 1) : d363798 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d363278, d363798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363278, d363798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363279 q = 1) : d363799 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d363279, d363799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363279, d363799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38164 (p : Pattern) (selected : d363822 p = 0) : d363867 p = 1 := by
  have h0 (q : Pattern) (selected : d359730 q = 0) : d361805 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d359730, d361805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37677 q selected
    | true =>
      simp only [d359730, d361805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37739 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d360137 q = 0) : d362094 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d360137, d362094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360137, d362094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37816 q selected
  have h3 (q : Pattern) (selected : d360138 q = 0) : d362095 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d360138, d362095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360138, d362095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d363820 q = 0) : d363865 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d363820, d363865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363820, d363865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d363821 q = 0) : d363866 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d363821, d363866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363821, d363866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d363822 q = 0) : d363867 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d363822, d363867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363822, d363867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro38165 (p : Pattern) (selected : d363828 p = 0) : d363873 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d363823 q = 0) : d363868 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d363823, d363868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38164 q selected
    | true =>
      simp only [d363823, d363868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363824 q = 0) : d363869 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d363824, d363869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363824, d363869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363825 q = 0) : d363870 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d363825, d363870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363825, d363870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363826 q = 0) : d363871 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d363826, d363871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363826, d363871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363827 q = 0) : d363872 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d363827, d363872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363827, d363872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363828 q = 0) : d363873 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d363828, d363873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363828, d363873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38166 (p : Pattern) (selected : d363834 p = 0) : d363879 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d363829 q = 0) : d363874 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d363829, d363874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38165 q selected
    | true =>
      simp only [d363829, d363874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363830 q = 0) : d363875 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d363830, d363875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363830, d363875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363831 q = 0) : d363876 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d363831, d363876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363831, d363876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363832 q = 0) : d363877 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d363832, d363877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363832, d363877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363833 q = 0) : d363878 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d363833, d363878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363833, d363878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363834 q = 0) : d363879 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d363834, d363879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363834, d363879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38167 (p : Pattern) (selected : d363840 p = 0) : d363885 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d363835 q = 0) : d363880 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d363835, d363880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38166 q selected
    | true =>
      simp only [d363835, d363880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363836 q = 0) : d363881 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d363836, d363881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363836, d363881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363837 q = 0) : d363882 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d363837, d363882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363837, d363882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363838 q = 0) : d363883 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d363838, d363883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363838, d363883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363839 q = 0) : d363884 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d363839, d363884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363839, d363884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363840 q = 0) : d363885 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d363840, d363885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363840, d363885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38168 (p : Pattern) (selected : d363846 p = 0) : d363891 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d363841 q = 0) : d363886 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d363841, d363886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38167 q selected
    | true =>
      simp only [d363841, d363886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363842 q = 0) : d363887 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d363842, d363887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363842, d363887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363843 q = 0) : d363888 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d363843, d363888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363843, d363888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363844 q = 0) : d363889 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d363844, d363889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363844, d363889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363845 q = 0) : d363890 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d363845, d363890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363845, d363890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363846 q = 0) : d363891 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d363846, d363891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363846, d363891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38169 (p : Pattern) (selected : d363852 p = 0) : d363897 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d363847 q = 0) : d363892 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d363847, d363892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38168 q selected
    | true =>
      simp only [d363847, d363892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363848 q = 0) : d363893 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d363848, d363893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363848, d363893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363849 q = 0) : d363894 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d363849, d363894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363849, d363894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363850 q = 0) : d363895 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d363850, d363895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363850, d363895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363851 q = 0) : d363896 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d363851, d363896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363851, d363896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363852 q = 0) : d363897 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d363852, d363897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363852, d363897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38170 (p : Pattern) (selected : d363858 p = 0) : d363903 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d363853 q = 0) : d363898 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d363853, d363898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38169 q selected
    | true =>
      simp only [d363853, d363898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363854 q = 0) : d363899 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d363854, d363899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363854, d363899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363855 q = 0) : d363900 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d363855, d363900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363855, d363900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363856 q = 0) : d363901 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d363856, d363901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363856, d363901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363857 q = 0) : d363902 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d363857, d363902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363857, d363902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363858 q = 0) : d363903 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d363858, d363903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363858, d363903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38171 (p : Pattern) (selected : d363864 p = 0) : d363909 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d363859 q = 0) : d363904 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d363859, d363904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38170 q selected
    | true =>
      simp only [d363859, d363904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363860 q = 0) : d363905 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d363860, d363905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363860, d363905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363861 q = 0) : d363906 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d363861, d363906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363861, d363906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363862 q = 0) : d363907 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d363862, d363907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363862, d363907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363863 q = 0) : d363908 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d363863, d363908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363863, d363908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363864 q = 0) : d363909 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d363864, d363909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363864, d363909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38172 (p : Pattern) (selected : d363822 p = 1) : d364354 p = 1 := by
  have h0 (q : Pattern) (selected : d359730 q = 1) : d363051 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d359730, d363051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38028 q selected
    | true =>
      simp only [d359730, d363051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38049 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d360137 q = 1) : d363091 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d360137, d363091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d360137, d363091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38077 q selected
  have h3 (q : Pattern) (selected : d360138 q = 1) : d363092 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d360138, d363092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d360138, d363092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d363820 q = 1) : d364352 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d363820, d364352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363820, d364352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d363821 q = 1) : d364353 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d363821, d364353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363821, d364353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d363822 q = 1) : d364354 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d363822, d364354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363822, d364354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro38173 (p : Pattern) (selected : d363828 p = 1) : d364360 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d363823 q = 1) : d364355 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d363823, d364355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38172 q selected
    | true =>
      simp only [d363823, d364355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363824 q = 1) : d364356 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d363824, d364356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363824, d364356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363825 q = 1) : d364357 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d363825, d364357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363825, d364357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363826 q = 1) : d364358 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d363826, d364358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363826, d364358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363827 q = 1) : d364359 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d363827, d364359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363827, d364359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363828 q = 1) : d364360 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d363828, d364360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363828, d364360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38174 (p : Pattern) (selected : d363834 p = 1) : d364366 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d363829 q = 1) : d364361 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d363829, d364361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38173 q selected
    | true =>
      simp only [d363829, d364361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363830 q = 1) : d364362 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d363830, d364362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363830, d364362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363831 q = 1) : d364363 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d363831, d364363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363831, d364363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363832 q = 1) : d364364 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d363832, d364364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363832, d364364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363833 q = 1) : d364365 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d363833, d364365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363833, d364365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363834 q = 1) : d364366 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d363834, d364366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363834, d364366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38175 (p : Pattern) (selected : d363840 p = 1) : d364372 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d363835 q = 1) : d364367 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d363835, d364367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38174 q selected
    | true =>
      simp only [d363835, d364367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363836 q = 1) : d364368 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d363836, d364368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363836, d364368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363837 q = 1) : d364369 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d363837, d364369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363837, d364369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363838 q = 1) : d364370 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d363838, d364370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363838, d364370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363839 q = 1) : d364371 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d363839, d364371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363839, d364371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363840 q = 1) : d364372 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d363840, d364372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363840, d364372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38176 (p : Pattern) (selected : d363846 p = 1) : d364378 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d363841 q = 1) : d364373 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d363841, d364373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38175 q selected
    | true =>
      simp only [d363841, d364373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363842 q = 1) : d364374 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d363842, d364374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363842, d364374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363843 q = 1) : d364375 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d363843, d364375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363843, d364375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363844 q = 1) : d364376 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d363844, d364376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363844, d364376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363845 q = 1) : d364377 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d363845, d364377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363845, d364377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363846 q = 1) : d364378 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d363846, d364378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363846, d364378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38177 (p : Pattern) (selected : d363852 p = 1) : d364384 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d363847 q = 1) : d364379 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d363847, d364379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38176 q selected
    | true =>
      simp only [d363847, d364379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363848 q = 1) : d364380 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d363848, d364380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363848, d364380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363849 q = 1) : d364381 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d363849, d364381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363849, d364381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363850 q = 1) : d364382 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d363850, d364382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363850, d364382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363851 q = 1) : d364383 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d363851, d364383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363851, d364383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363852 q = 1) : d364384 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d363852, d364384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363852, d364384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38178 (p : Pattern) (selected : d363858 p = 1) : d364390 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d363853 q = 1) : d364385 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d363853, d364385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38177 q selected
    | true =>
      simp only [d363853, d364385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363854 q = 1) : d364386 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d363854, d364386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363854, d364386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363855 q = 1) : d364387 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d363855, d364387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363855, d364387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363856 q = 1) : d364388 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d363856, d364388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363856, d364388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363857 q = 1) : d364389 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d363857, d364389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363857, d364389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363858 q = 1) : d364390 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d363858, d364390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363858, d364390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38179 (p : Pattern) (selected : d363864 p = 1) : d364396 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d363859 q = 1) : d364391 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d363859, d364391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38178 q selected
    | true =>
      simp only [d363859, d364391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363860 q = 1) : d364392 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d363860, d364392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d363860, d364392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d363861 q = 1) : d364393 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d363861, d364393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d363861, d364393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d363862 q = 1) : d364394 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d363862, d364394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d363862, d364394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d363863 q = 1) : d364395 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d363863, d364395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d363863, d364395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d363864 q = 1) : d364396 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d363864, d364396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d363864, d364396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38180 (p : Pattern) (selected : d364425 p = 0) : d364471 p = 1 := by
  have h0 (q : Pattern) (selected : d359730 q = 0) : d361805 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d359730, d361805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37677 q selected
    | true =>
      simp only [d359730, d361805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37739 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d364422 q = 0) : d364468 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d364422, d364468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d364422, d364468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d364423 q = 0) : d364469 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d364423, d364469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364423, d364469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d364424 q = 0) : d364470 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d364424, d364470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364424, d364470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d364425 q = 0) : d364471 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d364425, d364471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364425, d364471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro38181 (p : Pattern) (selected : d364431 p = 0) : d364477 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d364426 q = 0) : d364472 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d364426, d364472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38180 q selected
    | true =>
      simp only [d364426, d364472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364427 q = 0) : d364473 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d364427, d364473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364427, d364473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364428 q = 0) : d364474 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d364428, d364474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364428, d364474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364429 q = 0) : d364475 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d364429, d364475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364429, d364475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364430 q = 0) : d364476 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d364430, d364476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364430, d364476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364431 q = 0) : d364477 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d364431, d364477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364431, d364477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38182 (p : Pattern) (selected : d364437 p = 0) : d364483 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d364432 q = 0) : d364478 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d364432, d364478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38181 q selected
    | true =>
      simp only [d364432, d364478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364433 q = 0) : d364479 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d364433, d364479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364433, d364479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364434 q = 0) : d364480 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d364434, d364480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364434, d364480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364435 q = 0) : d364481 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d364435, d364481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364435, d364481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364436 q = 0) : d364482 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d364436, d364482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364436, d364482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364437 q = 0) : d364483 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d364437, d364483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364437, d364483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38183 (p : Pattern) (selected : d364443 p = 0) : d364489 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d364438 q = 0) : d364484 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d364438, d364484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38182 q selected
    | true =>
      simp only [d364438, d364484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364439 q = 0) : d364485 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d364439, d364485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364439, d364485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364440 q = 0) : d364486 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d364440, d364486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364440, d364486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364441 q = 0) : d364487 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d364441, d364487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364441, d364487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364442 q = 0) : d364488 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d364442, d364488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364442, d364488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364443 q = 0) : d364489 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d364443, d364489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364443, d364489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38184 (p : Pattern) (selected : d364449 p = 0) : d364495 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d364444 q = 0) : d364490 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d364444, d364490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38183 q selected
    | true =>
      simp only [d364444, d364490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364445 q = 0) : d364491 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d364445, d364491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364445, d364491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364446 q = 0) : d364492 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d364446, d364492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364446, d364492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364447 q = 0) : d364493 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d364447, d364493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364447, d364493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364448 q = 0) : d364494 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d364448, d364494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364448, d364494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364449 q = 0) : d364495 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d364449, d364495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364449, d364495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38185 (p : Pattern) (selected : d364455 p = 0) : d364501 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d364450 q = 0) : d364496 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d364450, d364496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38184 q selected
    | true =>
      simp only [d364450, d364496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364451 q = 0) : d364497 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d364451, d364497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364451, d364497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364452 q = 0) : d364498 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d364452, d364498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364452, d364498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364453 q = 0) : d364499 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d364453, d364499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364453, d364499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364454 q = 0) : d364500 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d364454, d364500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364454, d364500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364455 q = 0) : d364501 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d364455, d364501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364455, d364501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38186 (p : Pattern) (selected : d364461 p = 0) : d364507 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d364456 q = 0) : d364502 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d364456, d364502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38185 q selected
    | true =>
      simp only [d364456, d364502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364457 q = 0) : d364503 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d364457, d364503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364457, d364503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364458 q = 0) : d364504 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d364458, d364504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364458, d364504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364459 q = 0) : d364505 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d364459, d364505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364459, d364505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364460 q = 0) : d364506 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d364460, d364506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364460, d364506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364461 q = 0) : d364507 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d364461, d364507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364461, d364507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38187 (p : Pattern) (selected : d364467 p = 0) : d364513 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d364462 q = 0) : d364508 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d364462, d364508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38186 q selected
    | true =>
      simp only [d364462, d364508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364463 q = 0) : d364509 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d364463, d364509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364463, d364509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364464 q = 0) : d364510 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d364464, d364510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364464, d364510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364465 q = 0) : d364511 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d364465, d364511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364465, d364511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364466 q = 0) : d364512 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d364466, d364512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364466, d364512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364467 q = 0) : d364513 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d364467, d364513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364467, d364513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38188 (p : Pattern) (selected : d364425 p = 1) : d364893 p = 1 := by
  have h0 (q : Pattern) (selected : d359730 q = 1) : d363051 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d359730, d363051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38028 q selected
    | true =>
      simp only [d359730, d363051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38049 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d364422 q = 1) : d364890 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d364422, d364890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d364422, d364890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d364423 q = 1) : d364891 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d364423, d364891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364423, d364891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d364424 q = 1) : d364892 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d364424, d364892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364424, d364892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d364425 q = 1) : d364893 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d364425, d364893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364425, d364893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro38189 (p : Pattern) (selected : d364431 p = 1) : d364899 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d364426 q = 1) : d364894 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d364426, d364894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38188 q selected
    | true =>
      simp only [d364426, d364894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364427 q = 1) : d364895 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d364427, d364895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364427, d364895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364428 q = 1) : d364896 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d364428, d364896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364428, d364896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364429 q = 1) : d364897 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d364429, d364897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364429, d364897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364430 q = 1) : d364898 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d364430, d364898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364430, d364898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364431 q = 1) : d364899 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d364431, d364899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364431, d364899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38190 (p : Pattern) (selected : d364437 p = 1) : d364905 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d364432 q = 1) : d364900 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d364432, d364900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38189 q selected
    | true =>
      simp only [d364432, d364900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364433 q = 1) : d364901 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d364433, d364901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364433, d364901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364434 q = 1) : d364902 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d364434, d364902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364434, d364902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364435 q = 1) : d364903 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d364435, d364903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364435, d364903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364436 q = 1) : d364904 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d364436, d364904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364436, d364904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364437 q = 1) : d364905 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d364437, d364905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364437, d364905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38191 (p : Pattern) (selected : d364443 p = 1) : d364911 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d364438 q = 1) : d364906 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d364438, d364906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38190 q selected
    | true =>
      simp only [d364438, d364906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364439 q = 1) : d364907 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d364439, d364907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364439, d364907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364440 q = 1) : d364908 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d364440, d364908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364440, d364908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364441 q = 1) : d364909 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d364441, d364909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364441, d364909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364442 q = 1) : d364910 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d364442, d364910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364442, d364910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364443 q = 1) : d364911 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d364443, d364911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364443, d364911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38192 (p : Pattern) (selected : d364449 p = 1) : d364917 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d364444 q = 1) : d364912 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d364444, d364912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38191 q selected
    | true =>
      simp only [d364444, d364912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364445 q = 1) : d364913 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d364445, d364913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364445, d364913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364446 q = 1) : d364914 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d364446, d364914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364446, d364914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364447 q = 1) : d364915 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d364447, d364915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364447, d364915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364448 q = 1) : d364916 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d364448, d364916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364448, d364916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364449 q = 1) : d364917 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d364449, d364917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364449, d364917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38193 (p : Pattern) (selected : d364455 p = 1) : d364923 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d364450 q = 1) : d364918 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d364450, d364918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38192 q selected
    | true =>
      simp only [d364450, d364918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364451 q = 1) : d364919 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d364451, d364919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364451, d364919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364452 q = 1) : d364920 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d364452, d364920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364452, d364920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364453 q = 1) : d364921 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d364453, d364921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364453, d364921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364454 q = 1) : d364922 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d364454, d364922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364454, d364922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364455 q = 1) : d364923 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d364455, d364923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364455, d364923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38194 (p : Pattern) (selected : d364461 p = 1) : d364929 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d364456 q = 1) : d364924 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d364456, d364924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38193 q selected
    | true =>
      simp only [d364456, d364924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364457 q = 1) : d364925 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d364457, d364925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364457, d364925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364458 q = 1) : d364926 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d364458, d364926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364458, d364926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364459 q = 1) : d364927 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d364459, d364927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364459, d364927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364460 q = 1) : d364928 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d364460, d364928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364460, d364928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364461 q = 1) : d364929 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d364461, d364929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364461, d364929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38195 (p : Pattern) (selected : d364467 p = 1) : d364935 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d364462 q = 1) : d364930 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d364462, d364930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38194 q selected
    | true =>
      simp only [d364462, d364930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364463 q = 1) : d364931 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d364463, d364931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364463, d364931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364464 q = 1) : d364932 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d364464, d364932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364464, d364932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364465 q = 1) : d364933 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d364465, d364933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364465, d364933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364466 q = 1) : d364934 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d364466, d364934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364466, d364934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364467 q = 1) : d364935 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d364467, d364935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364467, d364935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38196 (p : Pattern) (selected : d364970 p = 0) : d365017 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d364966 q = 0) : d365013 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d364966, d365013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37677 q selected
    | true =>
      simp only [d364966, d365013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364967 q = 0) : d365014 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d364967, d365014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364967, d365014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364968 q = 0) : d365015 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d364968, d365015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364968, d365015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364969 q = 0) : d365016 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d364969, d365016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364969, d365016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364970 q = 0) : d365017 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d364970, d365017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364970, d365017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro38197 (p : Pattern) (selected : d364976 p = 0) : d365023 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d364971 q = 0) : d365018 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d364971, d365018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38196 q selected
    | true =>
      simp only [d364971, d365018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364972 q = 0) : d365019 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d364972, d365019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364972, d365019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364973 q = 0) : d365020 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d364973, d365020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364973, d365020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364974 q = 0) : d365021 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d364974, d365021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364974, d365021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364975 q = 0) : d365022 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d364975, d365022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364975, d365022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364976 q = 0) : d365023 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d364976, d365023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364976, d365023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38198 (p : Pattern) (selected : d364982 p = 0) : d365029 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d364977 q = 0) : d365024 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d364977, d365024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38197 q selected
    | true =>
      simp only [d364977, d365024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364978 q = 0) : d365025 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d364978, d365025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364978, d365025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364979 q = 0) : d365026 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d364979, d365026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364979, d365026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364980 q = 0) : d365027 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d364980, d365027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364980, d365027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364981 q = 0) : d365028 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d364981, d365028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364981, d365028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364982 q = 0) : d365029 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d364982, d365029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364982, d365029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38199 (p : Pattern) (selected : d364988 p = 0) : d365035 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d364983 q = 0) : d365030 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d364983, d365030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38198 q selected
    | true =>
      simp only [d364983, d365030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364984 q = 0) : d365031 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d364984, d365031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364984, d365031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364985 q = 0) : d365032 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d364985, d365032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364985, d365032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364986 q = 0) : d365033 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d364986, d365033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364986, d365033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364987 q = 0) : d365034 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d364987, d365034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364987, d365034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364988 q = 0) : d365035 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d364988, d365035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364988, d365035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38200 (p : Pattern) (selected : d364994 p = 0) : d365041 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d364989 q = 0) : d365036 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d364989, d365036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38199 q selected
    | true =>
      simp only [d364989, d365036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364990 q = 0) : d365037 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d364990, d365037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364990, d365037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364991 q = 0) : d365038 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d364991, d365038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364991, d365038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364992 q = 0) : d365039 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d364992, d365039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364992, d365039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364993 q = 0) : d365040 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d364993, d365040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364993, d365040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364994 q = 0) : d365041 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d364994, d365041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364994, d365041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38201 (p : Pattern) (selected : d365000 p = 0) : d365047 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d364995 q = 0) : d365042 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d364995, d365042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38200 q selected
    | true =>
      simp only [d364995, d365042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364996 q = 0) : d365043 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d364996, d365043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364996, d365043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364997 q = 0) : d365044 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d364997, d365044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364997, d365044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364998 q = 0) : d365045 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d364998, d365045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364998, d365045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364999 q = 0) : d365046 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d364999, d365046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364999, d365046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365000 q = 0) : d365047 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d365000, d365047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365000, d365047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38202 (p : Pattern) (selected : d365006 p = 0) : d365053 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d365001 q = 0) : d365048 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d365001, d365048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38201 q selected
    | true =>
      simp only [d365001, d365048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365002 q = 0) : d365049 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d365002, d365049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365002, d365049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365003 q = 0) : d365050 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d365003, d365050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365003, d365050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365004 q = 0) : d365051 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d365004, d365051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365004, d365051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365005 q = 0) : d365052 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d365005, d365052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365005, d365052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365006 q = 0) : d365053 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d365006, d365053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365006, d365053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38203 (p : Pattern) (selected : d365012 p = 0) : d365059 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d365007 q = 0) : d365054 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d365007, d365054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38202 q selected
    | true =>
      simp only [d365007, d365054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365008 q = 0) : d365055 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d365008, d365055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365008, d365055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365009 q = 0) : d365056 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d365009, d365056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365009, d365056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365010 q = 0) : d365057 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d365010, d365057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365010, d365057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365011 q = 0) : d365058 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d365011, d365058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365011, d365058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365012 q = 0) : d365059 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d365012, d365059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365012, d365059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38204 (p : Pattern) (selected : d364970 p = 1) : d365371 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d364966 q = 1) : d365367 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d364966, d365367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38028 q selected
    | true =>
      simp only [d364966, d365367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364967 q = 1) : d365368 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d364967, d365368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364967, d365368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364968 q = 1) : d365369 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d364968, d365369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364968, d365369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364969 q = 1) : d365370 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d364969, d365370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364969, d365370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364970 q = 1) : d365371 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d364970, d365371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364970, d365371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro38205 (p : Pattern) (selected : d364976 p = 1) : d365377 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d364971 q = 1) : d365372 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d364971, d365372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38204 q selected
    | true =>
      simp only [d364971, d365372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364972 q = 1) : d365373 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d364972, d365373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364972, d365373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364973 q = 1) : d365374 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d364973, d365374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364973, d365374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364974 q = 1) : d365375 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d364974, d365375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364974, d365375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364975 q = 1) : d365376 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d364975, d365376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364975, d365376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364976 q = 1) : d365377 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d364976, d365377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364976, d365377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38206 (p : Pattern) (selected : d364982 p = 1) : d365383 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d364977 q = 1) : d365378 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d364977, d365378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38205 q selected
    | true =>
      simp only [d364977, d365378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364978 q = 1) : d365379 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d364978, d365379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364978, d365379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364979 q = 1) : d365380 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d364979, d365380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364979, d365380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364980 q = 1) : d365381 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d364980, d365381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364980, d365381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364981 q = 1) : d365382 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d364981, d365382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364981, d365382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364982 q = 1) : d365383 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d364982, d365383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364982, d365383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38207 (p : Pattern) (selected : d364988 p = 1) : d365389 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d364983 q = 1) : d365384 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d364983, d365384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38206 q selected
    | true =>
      simp only [d364983, d365384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364984 q = 1) : d365385 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d364984, d365385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364984, d365385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364985 q = 1) : d365386 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d364985, d365386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364985, d365386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364986 q = 1) : d365387 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d364986, d365387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364986, d365387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364987 q = 1) : d365388 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d364987, d365388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364987, d365388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364988 q = 1) : d365389 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d364988, d365389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364988, d365389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38208 (p : Pattern) (selected : d364994 p = 1) : d365395 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d364989 q = 1) : d365390 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d364989, d365390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38207 q selected
    | true =>
      simp only [d364989, d365390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364990 q = 1) : d365391 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d364990, d365391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364990, d365391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364991 q = 1) : d365392 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d364991, d365392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364991, d365392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364992 q = 1) : d365393 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d364992, d365393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364992, d365393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364993 q = 1) : d365394 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d364993, d365394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364993, d365394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d364994 q = 1) : d365395 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d364994, d365395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d364994, d365395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38209 (p : Pattern) (selected : d365000 p = 1) : d365401 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d364995 q = 1) : d365396 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d364995, d365396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38208 q selected
    | true =>
      simp only [d364995, d365396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d364996 q = 1) : d365397 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d364996, d365397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d364996, d365397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d364997 q = 1) : d365398 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d364997, d365398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364997, d365398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d364998 q = 1) : d365399 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d364998, d365399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d364998, d365399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d364999 q = 1) : d365400 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d364999, d365400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d364999, d365400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365000 q = 1) : d365401 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d365000, d365401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365000, d365401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38210 (p : Pattern) (selected : d365006 p = 1) : d365407 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d365001 q = 1) : d365402 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d365001, d365402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38209 q selected
    | true =>
      simp only [d365001, d365402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365002 q = 1) : d365403 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d365002, d365403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365002, d365403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365003 q = 1) : d365404 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d365003, d365404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365003, d365404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365004 q = 1) : d365405 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d365004, d365405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365004, d365405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365005 q = 1) : d365406 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d365005, d365406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365005, d365406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365006 q = 1) : d365407 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d365006, d365407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365006, d365407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38211 (p : Pattern) (selected : d365012 p = 1) : d365413 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d365007 q = 1) : d365408 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d365007, d365408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38210 q selected
    | true =>
      simp only [d365007, d365408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365008 q = 1) : d365409 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d365008, d365409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365008, d365409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365009 q = 1) : d365410 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d365009, d365410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365009, d365410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365010 q = 1) : d365411 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d365010, d365411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365010, d365411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365011 q = 1) : d365412 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d365011, d365412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365011, d365412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365012 q = 1) : d365413 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d365012, d365413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365012, d365413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38212 (p : Pattern) (selected : d359195 p = 0) : d361399 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359018 q = 0) : d361271 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d359018, d361271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359018, d361271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37610 q selected
  have h2 (q : Pattern) (selected : d359019 q = 0) : d361272 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d359019, d361272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359019, d361272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359020 q = 0) : d361273 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d359020, d361273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359020, d361273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359021 q = 0) : d361274 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d359021, d361274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359021, d361274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359191 q = 0) : d361395 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d359191, d361395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359191, d361395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37640 q selected
  have h6 (q : Pattern) (selected : d359192 q = 0) : d361396 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d359192, d361396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359192, d361396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359193 q = 0) : d361397 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d359193, d361397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359193, d361397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359194 q = 0) : d361398 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d359194, d361398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359194, d361398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359195 q = 0) : d361399 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d359195, d361399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359195, d361399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38213 (p : Pattern) (selected : d365454 p = 0) : d365502 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d365449 q = 0) : d365497 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d365449, d365497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38212 q selected
    | true =>
      simp only [d365449, d365497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365450 q = 0) : d365498 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d365450, d365498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365450, d365498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365451 q = 0) : d365499 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d365451, d365499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365451, d365499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365452 q = 0) : d365500 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d365452, d365500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365452, d365500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365453 q = 0) : d365501 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d365453, d365501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365453, d365501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365454 q = 0) : d365502 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d365454, d365502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365454, d365502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38214 (p : Pattern) (selected : d365460 p = 0) : d365508 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d365455 q = 0) : d365503 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d365455, d365503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38213 q selected
    | true =>
      simp only [d365455, d365503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365456 q = 0) : d365504 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d365456, d365504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365456, d365504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365457 q = 0) : d365505 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d365457, d365505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365457, d365505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365458 q = 0) : d365506 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d365458, d365506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365458, d365506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365459 q = 0) : d365507 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d365459, d365507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365459, d365507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365460 q = 0) : d365508 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d365460, d365508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365460, d365508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38215 (p : Pattern) (selected : d365466 p = 0) : d365514 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d365461 q = 0) : d365509 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d365461, d365509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38214 q selected
    | true =>
      simp only [d365461, d365509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365462 q = 0) : d365510 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d365462, d365510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365462, d365510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365463 q = 0) : d365511 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d365463, d365511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365463, d365511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365464 q = 0) : d365512 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d365464, d365512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365464, d365512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365465 q = 0) : d365513 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d365465, d365513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365465, d365513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365466 q = 0) : d365514 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d365466, d365514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365466, d365514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38216 (p : Pattern) (selected : d365472 p = 0) : d365520 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d365467 q = 0) : d365515 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d365467, d365515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38215 q selected
    | true =>
      simp only [d365467, d365515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365468 q = 0) : d365516 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d365468, d365516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365468, d365516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365469 q = 0) : d365517 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d365469, d365517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365469, d365517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365470 q = 0) : d365518 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d365470, d365518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365470, d365518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365471 q = 0) : d365519 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d365471, d365519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365471, d365519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365472 q = 0) : d365520 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d365472, d365520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365472, d365520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38217 (p : Pattern) (selected : d365478 p = 0) : d365526 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d365473 q = 0) : d365521 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d365473, d365521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38216 q selected
    | true =>
      simp only [d365473, d365521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365474 q = 0) : d365522 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d365474, d365522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365474, d365522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365475 q = 0) : d365523 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d365475, d365523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365475, d365523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365476 q = 0) : d365524 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d365476, d365524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365476, d365524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365477 q = 0) : d365525 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d365477, d365525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365477, d365525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365478 q = 0) : d365526 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d365478, d365526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365478, d365526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38218 (p : Pattern) (selected : d365484 p = 0) : d365532 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d365479 q = 0) : d365527 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d365479, d365527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38217 q selected
    | true =>
      simp only [d365479, d365527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365480 q = 0) : d365528 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d365480, d365528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365480, d365528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365481 q = 0) : d365529 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d365481, d365529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365481, d365529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365482 q = 0) : d365530 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d365482, d365530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365482, d365530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365483 q = 0) : d365531 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d365483, d365531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365483, d365531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365484 q = 0) : d365532 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d365484, d365532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365484, d365532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38219 (p : Pattern) (selected : d365490 p = 0) : d365538 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d365485 q = 0) : d365533 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d365485, d365533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38218 q selected
    | true =>
      simp only [d365485, d365533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365486 q = 0) : d365534 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d365486, d365534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365486, d365534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365487 q = 0) : d365535 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d365487, d365535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365487, d365535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365488 q = 0) : d365536 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d365488, d365536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365488, d365536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365489 q = 0) : d365537 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d365489, d365537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365489, d365537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365490 q = 0) : d365538 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d365490, d365538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365490, d365538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38220 (p : Pattern) (selected : d365496 p = 0) : d365544 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d365491 q = 0) : d365539 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d365491, d365539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38219 q selected
    | true =>
      simp only [d365491, d365539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365492 q = 0) : d365540 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d365492, d365540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365492, d365540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365493 q = 0) : d365541 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d365493, d365541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365493, d365541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365494 q = 0) : d365542 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d365494, d365542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365494, d365542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365495 q = 0) : d365543 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d365495, d365543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365495, d365543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365496 q = 0) : d365544 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d365496, d365544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365496, d365544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38221 (p : Pattern) (selected : d359195 p = 1) : d362972 p = 1 := by
  have h0 (q : Pattern) (selected : d359021 q = 1) : d359021 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d359191 q = 1) : d362968 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d359191, d362968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359191, d362968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38013 q selected
  have h3 (q : Pattern) (selected : d359192 q = 1) : d362969 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d359192, d362969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359192, d362969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359193 q = 1) : d362970 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d359193, d362970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359193, d362970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359194 q = 1) : d362971 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d359194, d362971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359194, d362971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359195 q = 1) : d362972 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d359195, d362972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359195, d362972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38222 (p : Pattern) (selected : d365454 p = 1) : d365727 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d365449 q = 1) : d365722 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d365449, d365722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38221 q selected
    | true =>
      simp only [d365449, d365722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365450 q = 1) : d365723 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d365450, d365723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365450, d365723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365451 q = 1) : d365724 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d365451, d365724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365451, d365724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365452 q = 1) : d365725 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d365452, d365725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365452, d365725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365453 q = 1) : d365726 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d365453, d365726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365453, d365726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365454 q = 1) : d365727 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d365454, d365727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365454, d365727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38223 (p : Pattern) (selected : d365460 p = 1) : d365733 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d365455 q = 1) : d365728 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d365455, d365728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38222 q selected
    | true =>
      simp only [d365455, d365728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365456 q = 1) : d365729 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d365456, d365729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365456, d365729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365457 q = 1) : d365730 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d365457, d365730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365457, d365730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365458 q = 1) : d365731 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d365458, d365731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365458, d365731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365459 q = 1) : d365732 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d365459, d365732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365459, d365732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365460 q = 1) : d365733 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d365460, d365733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365460, d365733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38224 (p : Pattern) (selected : d365466 p = 1) : d365739 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d365461 q = 1) : d365734 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d365461, d365734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38223 q selected
    | true =>
      simp only [d365461, d365734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365462 q = 1) : d365735 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d365462, d365735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365462, d365735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365463 q = 1) : d365736 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d365463, d365736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365463, d365736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365464 q = 1) : d365737 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d365464, d365737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365464, d365737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365465 q = 1) : d365738 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d365465, d365738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365465, d365738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365466 q = 1) : d365739 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d365466, d365739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365466, d365739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38225 (p : Pattern) (selected : d365472 p = 1) : d365745 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d365467 q = 1) : d365740 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d365467, d365740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38224 q selected
    | true =>
      simp only [d365467, d365740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365468 q = 1) : d365741 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d365468, d365741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365468, d365741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365469 q = 1) : d365742 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d365469, d365742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365469, d365742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365470 q = 1) : d365743 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d365470, d365743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365470, d365743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365471 q = 1) : d365744 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d365471, d365744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365471, d365744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365472 q = 1) : d365745 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d365472, d365745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365472, d365745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38226 (p : Pattern) (selected : d365478 p = 1) : d365751 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d365473 q = 1) : d365746 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d365473, d365746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38225 q selected
    | true =>
      simp only [d365473, d365746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365474 q = 1) : d365747 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d365474, d365747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365474, d365747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365475 q = 1) : d365748 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d365475, d365748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365475, d365748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365476 q = 1) : d365749 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d365476, d365749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365476, d365749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365477 q = 1) : d365750 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d365477, d365750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365477, d365750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365478 q = 1) : d365751 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d365478, d365751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365478, d365751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38227 (p : Pattern) (selected : d365484 p = 1) : d365757 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d365479 q = 1) : d365752 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d365479, d365752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38226 q selected
    | true =>
      simp only [d365479, d365752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365480 q = 1) : d365753 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d365480, d365753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365480, d365753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365481 q = 1) : d365754 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d365481, d365754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365481, d365754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365482 q = 1) : d365755 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d365482, d365755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365482, d365755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365483 q = 1) : d365756 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d365483, d365756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365483, d365756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365484 q = 1) : d365757 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d365484, d365757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365484, d365757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38228 (p : Pattern) (selected : d365490 p = 1) : d365763 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d365485 q = 1) : d365758 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d365485, d365758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38227 q selected
    | true =>
      simp only [d365485, d365758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365486 q = 1) : d365759 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d365486, d365759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365486, d365759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365487 q = 1) : d365760 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d365487, d365760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365487, d365760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365488 q = 1) : d365761 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d365488, d365761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365488, d365761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365489 q = 1) : d365762 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d365489, d365762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365489, d365762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365490 q = 1) : d365763 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d365490, d365763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365490, d365763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38229 (p : Pattern) (selected : d365496 p = 1) : d365769 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d365491 q = 1) : d365764 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d365491, d365764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38228 q selected
    | true =>
      simp only [d365491, d365764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365492 q = 1) : d365765 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d365492, d365765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365492, d365765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365493 q = 1) : d365766 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d365493, d365766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365493, d365766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365494 q = 1) : d365767 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d365494, d365767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365494, d365767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365495 q = 1) : d365768 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d365495, d365768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365495, d365768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365496 q = 1) : d365769 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d365496, d365769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365496, d365769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38230 (p : Pattern) (selected : d365810 p = 0) : d365859 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359018 q = 0) : d361271 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d359018, d361271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359018, d361271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37610 q selected
  have h2 (q : Pattern) (selected : d359019 q = 0) : d361272 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d359019, d361272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359019, d361272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359020 q = 0) : d361273 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d359020, d361273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359020, d361273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359021 q = 0) : d361274 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d359021, d361274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359021, d361274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d365810 q = 0) : d365859 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d365810, d365859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365810, d365859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro38231 (p : Pattern) (selected : d365816 p = 0) : d365865 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d365811 q = 0) : d365860 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d365811, d365860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38230 q selected
    | true =>
      simp only [d365811, d365860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365812 q = 0) : d365861 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d365812, d365861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365812, d365861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365813 q = 0) : d365862 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d365813, d365862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365813, d365862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365814 q = 0) : d365863 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d365814, d365863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365814, d365863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365815 q = 0) : d365864 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d365815, d365864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365815, d365864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365816 q = 0) : d365865 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d365816, d365865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365816, d365865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38232 (p : Pattern) (selected : d365822 p = 0) : d365871 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d365817 q = 0) : d365866 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d365817, d365866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38231 q selected
    | true =>
      simp only [d365817, d365866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365818 q = 0) : d365867 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d365818, d365867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365818, d365867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365819 q = 0) : d365868 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d365819, d365868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365819, d365868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365820 q = 0) : d365869 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d365820, d365869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365820, d365869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365821 q = 0) : d365870 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d365821, d365870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365821, d365870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365822 q = 0) : d365871 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d365822, d365871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365822, d365871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38233 (p : Pattern) (selected : d365828 p = 0) : d365877 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d365823 q = 0) : d365872 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d365823, d365872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38232 q selected
    | true =>
      simp only [d365823, d365872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365824 q = 0) : d365873 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d365824, d365873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365824, d365873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365825 q = 0) : d365874 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d365825, d365874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365825, d365874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365826 q = 0) : d365875 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d365826, d365875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365826, d365875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365827 q = 0) : d365876 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d365827, d365876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365827, d365876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365828 q = 0) : d365877 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d365828, d365877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365828, d365877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38234 (p : Pattern) (selected : d365834 p = 0) : d365883 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d365829 q = 0) : d365878 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d365829, d365878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38233 q selected
    | true =>
      simp only [d365829, d365878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365830 q = 0) : d365879 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d365830, d365879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365830, d365879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365831 q = 0) : d365880 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d365831, d365880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365831, d365880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365832 q = 0) : d365881 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d365832, d365881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365832, d365881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365833 q = 0) : d365882 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d365833, d365882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365833, d365882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365834 q = 0) : d365883 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d365834, d365883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365834, d365883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38235 (p : Pattern) (selected : d365840 p = 0) : d365889 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d365835 q = 0) : d365884 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d365835, d365884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38234 q selected
    | true =>
      simp only [d365835, d365884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365836 q = 0) : d365885 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d365836, d365885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365836, d365885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365837 q = 0) : d365886 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d365837, d365886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365837, d365886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365838 q = 0) : d365887 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d365838, d365887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365838, d365887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365839 q = 0) : d365888 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d365839, d365888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365839, d365888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365840 q = 0) : d365889 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d365840, d365889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365840, d365889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38236 (p : Pattern) (selected : d365846 p = 0) : d365895 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d365841 q = 0) : d365890 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d365841, d365890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38235 q selected
    | true =>
      simp only [d365841, d365890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365842 q = 0) : d365891 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d365842, d365891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365842, d365891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365843 q = 0) : d365892 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d365843, d365892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365843, d365892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365844 q = 0) : d365893 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d365844, d365893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365844, d365893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365845 q = 0) : d365894 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d365845, d365894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365845, d365894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365846 q = 0) : d365895 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d365846, d365895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365846, d365895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38237 (p : Pattern) (selected : d365852 p = 0) : d365901 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d365847 q = 0) : d365896 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d365847, d365896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38236 q selected
    | true =>
      simp only [d365847, d365896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365848 q = 0) : d365897 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d365848, d365897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365848, d365897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365849 q = 0) : d365898 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d365849, d365898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365849, d365898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365850 q = 0) : d365899 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d365850, d365899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365850, d365899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365851 q = 0) : d365900 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d365851, d365900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365851, d365900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365852 q = 0) : d365901 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d365852, d365901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365852, d365901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38238 (p : Pattern) (selected : d365858 p = 0) : d365907 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d365853 q = 0) : d365902 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d365853, d365902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38237 q selected
    | true =>
      simp only [d365853, d365902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d365854 q = 0) : d365903 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d365854, d365903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d365854, d365903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d365855 q = 0) : d365904 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d365855, d365904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d365855, d365904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d365856 q = 0) : d365905 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d365856, d365905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d365856, d365905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d365857 q = 0) : d365906 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d365857, d365906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d365857, d365906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d365858 q = 0) : d365907 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d365858, d365907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365858, d365907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38239 (p : Pattern) (selected : d365858 p = 1) : d365858 p = 1 := by
  have h0 (q : Pattern) (selected : d365858 q = 1) : d365858 q = 1 := by
    exact selected
  exact h0 p selected
theorem eqIntro38240 (p : Pattern) (selected : d44884 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1 q = 2) : d0 q = 1 := by
    change (1 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d13 q = 2) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44880 q = 2) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d44880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14 q = 2) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44881 q = 2) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d44881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15 q = 2) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44882 q = 2) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d44882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d16 q = 2) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44883 q = 2) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d44883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17 q = 2) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d17, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d44884 q = 2) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d44884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38241 (p : Pattern) (selected : d44890 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44885 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38240 q selected
    | true =>
      simp only [d44885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44886 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d19 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro644 q selected
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44887 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d21 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44888 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44889 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d22 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d23 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d44890 q = 2) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38242 (p : Pattern) (selected : d44896 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44891 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38241 q selected
    | true =>
      simp only [d44891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44892 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44893 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44894 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d26 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d27 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d28 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44895 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d29 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d44896 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38243 (p : Pattern) (selected : d44902 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44897 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38242 q selected
    | true =>
      simp only [d44897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro646 q selected
  have h2 (q : Pattern) (selected : d44898 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44899 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d31 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro646 q selected
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44900 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d34 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44901 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44902 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38244 (p : Pattern) (selected : d44908 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44903 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38243 q selected
    | true =>
      simp only [d44903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44904 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro647 q selected
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44905 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44906 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44907 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44908 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38245 (p : Pattern) (selected : d44914 p = 2) : d104 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d117 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro660 q selected
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d119 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d120 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d124 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro661 q selected
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d125 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d126 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44909 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38244 q selected
    | true =>
      simp only [d44909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
  have h9 (q : Pattern) (selected : d188 q = 2) : d43 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro671 q selected
    | true =>
      simp only [d188, d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d44910 q = 2) : d100 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44910, d100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44910, d100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d43 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d44911 q = 2) : d101 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44911, d101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44911, d101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d44912 q = 2) : d102 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44912, d102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44912, d102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d44913 q = 2) : d103 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44913, d103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44913, d103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d44914 q = 2) : d104 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44914, d104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44914, d104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro38246 (p : Pattern) (selected : d44915 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44903 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38243 q selected
    | true =>
      simp only [d44903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44904 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro647 q selected
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44905 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44906 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44907 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44915 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38247 (p : Pattern) (selected : d44921 p = 2) : d111 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d117 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro660 q selected
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d119 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d120 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d124 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro661 q selected
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d125 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d126 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44909 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38244 q selected
    | true =>
      simp only [d44909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
  have h9 (q : Pattern) (selected : d188 q = 2) : d43 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro671 q selected
    | true =>
      simp only [d188, d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d44910 q = 2) : d100 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44910, d100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44910, d100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d43 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d44911 q = 2) : d101 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44911, d101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44911, d101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d44912 q = 2) : d102 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44912, d102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44912, d102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d44913 q = 2) : d103 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44913, d103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44913, d103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d195 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro673 q selected
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d196 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d197 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d198 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d200 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro674 q selected
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d201 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d202 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d44916 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38246 q selected
    | true =>
      simp only [d44916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro650 q selected
  have h24 (q : Pattern) (selected : d206 q = 2) : d50 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro676 q selected
    | true =>
      simp only [d206, d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d44917 q = 2) : d107 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44917, d107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d44917, d107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d50 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro650 q selected
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d51 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d44918 q = 2) : d108 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44918, d108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d44918, d108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d44919 q = 2) : d109 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44919, d109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d44919, d109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d44920 q = 2) : d110 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44920, d110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d44920, d110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d44921 q = 2) : d111 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44921, d111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d44921, d111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro38248 (p : Pattern) (selected : d44928 p = 2) : d406 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44916 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38246 q selected
    | true =>
      simp only [d44916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro650 q selected
  have h2 (q : Pattern) (selected : d206 q = 2) : d50 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro676 q selected
    | true =>
      simp only [d206, d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44917 q = 2) : d107 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44917, d107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44917, d107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d50 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro650 q selected
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d51 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44918 q = 2) : d108 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44918, d108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44918, d108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44926 q = 2) : d109 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44926, d109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44926, d109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44927 q = 2) : d110 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44927, d110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44927, d110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d44928 q = 2) : d406 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44928, d406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44928, d406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38249 (p : Pattern) (selected : d44939 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44934 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38241 q selected
  have h2 (q : Pattern) (selected : d44891 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38241 q selected
    | true =>
      simp only [d44891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44935 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44892 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44936 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44937 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d66 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
  have h8 (q : Pattern) (selected : d25 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d67 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d26 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d68 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d69 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d44938 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d70 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d44939 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d44939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
end NetHack.Soko22Hazard87
