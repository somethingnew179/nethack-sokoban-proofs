import NetHack.Soko22Hazard87.EqIntroBlocks0083
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro21000 (p : Pattern) (selected : d214309 p = 0) : d215934 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214177 q = 0) : d215838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214177, d215838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20970 q selected
    | true =>
      simp only [d214177, d215838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214178 q = 0) : d215839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214178, d215839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214178, d215839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214181 q = 0) : d215842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20971 q selected
    | true =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214182 q = 0) : d215843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214183 q = 0) : d215844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214183, d215844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214183, d215844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214184 q = 0) : d215845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214184, d215845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214184, d215845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214210 q = 0) : d215871 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214210, d215871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214210, d215871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214309 q = 0) : d215934 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214309, d215934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214309, d215934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21001 (p : Pattern) (selected : d214310 p = 0) : d215935 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214181 q = 0) : d215842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20971 q selected
    | true =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214182 q = 0) : d215843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214187 q = 0) : d215848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214187, d215848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214187, d215848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214188 q = 0) : d215849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214188, d215849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214188, d215849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214212 q = 0) : d215873 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214212, d215873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214212, d215873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214310 q = 0) : d215935 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214310, d215935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214310, d215935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21002 (p : Pattern) (selected : d214315 p = 0) : d215940 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214177 q = 0) : d215838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214177, d215838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20970 q selected
    | true =>
      simp only [d214177, d215838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214178 q = 0) : d215839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214178, d215839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214178, d215839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214181 q = 0) : d215842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20971 q selected
    | true =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214182 q = 0) : d215843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214183 q = 0) : d215844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214183, d215844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214183, d215844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214218 q = 0) : d215879 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214218, d215879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214218, d215879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214219 q = 0) : d215880 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214219, d215880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214219, d215880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214315 q = 0) : d215940 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214315, d215940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214315, d215940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21003 (p : Pattern) (selected : d214316 p = 0) : d215941 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214181 q = 0) : d215842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20971 q selected
    | true =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214182 q = 0) : d215843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214187 q = 0) : d215848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214187, d215848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214187, d215848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214221 q = 0) : d215882 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214221, d215882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214221, d215882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214222 q = 0) : d215883 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214222, d215883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214222, d215883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214316 q = 0) : d215941 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214316, d215941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214316, d215941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21004 (p : Pattern) (selected : d214320 p = 0) : d215945 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214238 q = 0) : d215899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214238, d215899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20984 q selected
    | true =>
      simp only [d214238, d215899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214239 q = 0) : d215900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214239, d215900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214239, d215900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214243 q = 0) : d215904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214243, d215904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20985 q selected
    | true =>
      simp only [d214243, d215904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214244 q = 0) : d215905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214244, d215905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214244, d215905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214245 q = 0) : d215906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214245, d215906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214245, d215906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214246 q = 0) : d215907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214246, d215907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214246, d215907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214247 q = 0) : d215908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214247, d215908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214247, d215908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214320 q = 0) : d215945 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214320, d215945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214320, d215945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21005 (p : Pattern) (selected : d214321 p = 0) : d215946 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214243 q = 0) : d215904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214243, d215904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20985 q selected
    | true =>
      simp only [d214243, d215904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214244 q = 0) : d215905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214244, d215905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214244, d215905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214181 q = 0) : d215842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20971 q selected
    | true =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214182 q = 0) : d215843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214249 q = 0) : d215910 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214249, d215910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214249, d215910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214250 q = 0) : d215911 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214250, d215911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214250, d215911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214251 q = 0) : d215912 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214251, d215912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214251, d215912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214321 q = 0) : d215946 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214321, d215946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214321, d215946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21006 (p : Pattern) (selected : d214323 p = 0) : d215860 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214275 q = 0) : d215838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214275, d215838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20992 q selected
    | true =>
      simp only [d214275, d215838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214276 q = 0) : d215839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214276, d215839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214276, d215839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214279 q = 0) : d215842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214279, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20993 q selected
    | true =>
      simp only [d214279, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214280 q = 0) : d215843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214280, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214280, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214281 q = 0) : d215844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214281, d215844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214281, d215844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214282 q = 0) : d215845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214282, d215845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214282, d215845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214283 q = 0) : d215846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214283, d215846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214283, d215846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214323 q = 0) : d215860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214323, d215860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214323, d215860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21007 (p : Pattern) (selected : d214324 p = 0) : d215861 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214279 q = 0) : d215842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214279, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20993 q selected
    | true =>
      simp only [d214279, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214280 q = 0) : d215843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214280, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214280, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214285 q = 0) : d215848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214285, d215848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214285, d215848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214286 q = 0) : d215849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214286, d215849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214286, d215849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214287 q = 0) : d215850 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214287, d215850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214287, d215850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214324 q = 0) : d215861 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214324, d215861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214324, d215861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21008 (p : Pattern) (selected : d214327 p = 0) : d215949 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214297 q = 0) : d215922 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214297, d215922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20997 q selected
    | true =>
      simp only [d214297, d215922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214298 q = 0) : d215923 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214298, d215923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214298, d215923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214299 q = 0) : d215924 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214299, d215924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214299, d215924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214300 q = 0) : d215925 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214300, d215925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214300, d215925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214301 q = 0) : d215926 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214301, d215926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214301, d215926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214327 q = 0) : d215949 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214327, d215949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214327, d215949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21009 (p : Pattern) (selected : d214333 p = 0) : d215955 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214214 q = 0) : d215875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214214, d215875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20978 q selected
    | true =>
      simp only [d214214, d215875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20979 q selected
  have h2 (q : Pattern) (selected : d214215 q = 0) : d215876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214215, d215876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214215, d215876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214216 q = 0) : d215877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214216, d215877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214216, d215877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214217 q = 0) : d215878 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214217, d215878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214217, d215878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214224 q = 0) : d215885 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214224, d215885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20980 q selected
    | true =>
      simp only [d214224, d215885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20981 q selected
  have h6 (q : Pattern) (selected : d214225 q = 0) : d215886 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214225, d215886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214225, d215886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214226 q = 0) : d215887 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214226, d215887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214226, d215887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214253 q = 0) : d215914 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214253, d215914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20986 q selected
    | true =>
      simp only [d214253, d215914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20987 q selected
  have h9 (q : Pattern) (selected : d214289 q = 0) : d215852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214289, d215852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20994 q selected
    | true =>
      simp only [d214289, d215852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20995 q selected
  have h10 (q : Pattern) (selected : d214290 q = 0) : d215915 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214290, d215915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d214290, d215915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214303 q = 0) : d215928 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214303, d215928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20998 q selected
    | true =>
      simp only [d214303, d215928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d214304 q = 0) : d215929 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214304, d215929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214304, d215929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d214305 q = 0) : d215930 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214305, d215930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d214305, d215930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d214306 q = 0) : d215931 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214306, d215931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214306, d215931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d214307 q = 0) : d215932 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214307, d215932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214307, d215932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d214311 q = 0) : d215936 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214311, d215936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21000 q selected
    | true =>
      simp only [d214311, d215936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21001 q selected
  have h17 (q : Pattern) (selected : d214312 q = 0) : d215937 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214312, d215937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214312, d215937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d214313 q = 0) : d215938 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214313, d215938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d214313, d215938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d214314 q = 0) : d215939 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214314, d215939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214314, d215939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d214317 q = 0) : d215942 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214317, d215942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21002 q selected
    | true =>
      simp only [d214317, d215942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21003 q selected
  have h21 (q : Pattern) (selected : d214318 q = 0) : d215943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214318, d215943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214318, d215943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d214319 q = 0) : d215944 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214319, d215944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d214319, d215944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d214322 q = 0) : d215947 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214322, d215947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21004 q selected
    | true =>
      simp only [d214322, d215947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21005 q selected
  have h24 (q : Pattern) (selected : d214325 q = 0) : d215862 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214325, d215862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21006 q selected
    | true =>
      simp only [d214325, d215862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21007 q selected
  have h25 (q : Pattern) (selected : d214326 q = 0) : d215948 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214326, d215948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d214326, d215948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d214328 q = 0) : d215950 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214328, d215950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21008 q selected
    | true =>
      simp only [d214328, d215950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d214329 q = 0) : d215951 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214329, d215951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d214329, d215951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d214330 q = 0) : d215952 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214330, d215952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d214330, d215952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d214331 q = 0) : d215953 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214331, d215953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d214331, d215953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d214332 q = 0) : d215954 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214332, d215954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d214332, d215954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d214333 q = 0) : d215955 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214333, d215955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d214333, d215955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro21010 (p : Pattern) (selected : d214345 p = 0) : d215967 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214335 q = 0) : d215957 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214335, d215957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20987 q selected
    | true =>
      simp only [d214335, d215957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20973 q selected
  have h2 (q : Pattern) (selected : d214336 q = 0) : d215958 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214336, d215958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214336, d215958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214337 q = 0) : d215959 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214337, d215959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214337, d215959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214338 q = 0) : d215960 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214338, d215960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214338, d215960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214339 q = 0) : d215961 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214339, d215961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214339, d215961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214340 q = 0) : d215962 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214340, d215962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20973 q selected
    | true =>
      simp only [d214340, d215962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214341 q = 0) : d215963 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214341, d215963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214341, d215963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214342 q = 0) : d215964 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214342, d215964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214342, d215964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214343 q = 0) : d215965 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214343, d215965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214343, d215965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214344 q = 0) : d215966 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214344, d215966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214344, d215966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214345 q = 0) : d215967 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214345, d215967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214345, d215967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21011 (p : Pattern) (selected : d214351 p = 0) : d215973 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214340 q = 0) : d215962 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214340, d215962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20973 q selected
    | true =>
      simp only [d214340, d215962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214341 q = 0) : d215963 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214341, d215963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214341, d215963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214342 q = 0) : d215964 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214342, d215964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214342, d215964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214343 q = 0) : d215965 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214343, d215965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214343, d215965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214344 q = 0) : d215966 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214344, d215966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214344, d215966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214346 q = 0) : d215968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214346, d215968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20976 q selected
    | true =>
      simp only [d214346, d215968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214347 q = 0) : d215969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214347, d215969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214347, d215969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214348 q = 0) : d215970 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214348, d215970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214348, d215970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214349 q = 0) : d215971 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214349, d215971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214349, d215971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214350 q = 0) : d215972 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214350, d215972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214350, d215972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214351 q = 0) : d215973 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214351, d215973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214351, d215973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21012 (p : Pattern) (selected : d214358 p = 0) : d215980 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214322 q = 0) : d215947 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214322, d215947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21004 q selected
    | true =>
      simp only [d214322, d215947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21005 q selected
  have h2 (q : Pattern) (selected : d214325 q = 0) : d215862 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214325, d215862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21006 q selected
    | true =>
      simp only [d214325, d215862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21007 q selected
  have h3 (q : Pattern) (selected : d214326 q = 0) : d215948 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214326, d215948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214326, d215948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d214328 q = 0) : d215950 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214328, d215950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21008 q selected
    | true =>
      simp only [d214328, d215950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214329 q = 0) : d215951 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214329, d215951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214329, d215951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214330 q = 0) : d215952 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214330, d215952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214330, d215952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214356 q = 0) : d215978 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214356, d215978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214356, d215978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214357 q = 0) : d215979 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214357, d215979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214357, d215979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d214358 q = 0) : d215980 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214358, d215980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214358, d215980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21013 (p : Pattern) (selected : d214360 p = 0) : d215982 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214346 q = 0) : d215968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214346, d215968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20976 q selected
    | true =>
      simp only [d214346, d215968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214347 q = 0) : d215969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214347, d215969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214347, d215969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214348 q = 0) : d215970 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214348, d215970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214348, d215970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214349 q = 0) : d215971 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214349, d215971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214349, d215971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214350 q = 0) : d215972 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214350, d215972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214350, d215972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214360 q = 0) : d215982 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214360, d215982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214360, d215982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21014 (p : Pattern) (selected : d214368 p = 0) : d215990 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2331 q = 0) : d53496 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2331, d53496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2331, d53496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro576 q selected
  have h2 (q : Pattern) (selected : d2144 q = 0) : d53423 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro576 q selected
    | true =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2332 q = 0) : d53497 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2332, d53497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2332, d53497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2145 q = 0) : d53424 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2333 q = 0) : d53498 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2333, d53498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2333, d53498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17369 q = 0) : d128031 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6755 q selected
  have h7 (q : Pattern) (selected : d10343 q = 0) : d101664 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6755 q selected
    | true =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17370 q = 0) : d128032 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, d128032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17370, d128032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10345 q = 0) : d101666 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17371 q = 0) : d128033 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17371, d128033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17371, d128033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214366 q = 0) : d215988 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214366, d215988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214366, d215988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d13813 q = 0) : d113965 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
  have h13 (q : Pattern) (selected : d10353 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d13814 q = 0) : d113966 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10355 q = 0) : d101676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d13815 q = 0) : d113967 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d214367 q = 0) : d215989 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214367, d215989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214367, d215989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d214368 q = 0) : d215990 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214368, d215990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214368, d215990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro21015 (p : Pattern) (selected : d214371 p = 0) : d215993 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2335 q = 0) : d53500 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro553 q selected
  have h2 (q : Pattern) (selected : d2035 q = 0) : d53314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro553 q selected
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2336 q = 0) : d53501 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, d53501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2336, d53501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2036 q = 0) : d53315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2337 q = 0) : d53502 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, d53502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2337, d53502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17376 q = 0) : d128038 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6758 q selected
  have h7 (q : Pattern) (selected : d10364 q = 0) : d101685 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6758 q selected
    | true =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17377 q = 0) : d128039 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d128039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17377, d128039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10366 q = 0) : d101687 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17378 q = 0) : d128040 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d128040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17378, d128040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214369 q = 0) : d215991 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214369, d215991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214369, d215991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d13813 q = 0) : d113965 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
  have h13 (q : Pattern) (selected : d10353 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d13814 q = 0) : d113966 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10355 q = 0) : d101676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d13815 q = 0) : d113967 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d15775 q = 0) : d123728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
  have h18 (q : Pattern) (selected : d10371 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d15776 q = 0) : d123729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10373 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d15777 q = 0) : d123730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d123730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d15777, d123730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d214370 q = 0) : d215992 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214370, d215992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d214370, d215992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d214371 q = 0) : d215993 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214371, d215993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214371, d215993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro21016 (p : Pattern) (selected : d214375 p = 0) : d215997 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13813 q = 0) : d113965 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
  have h2 (q : Pattern) (selected : d10353 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13814 q = 0) : d113966 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10355 q = 0) : d101676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13815 q = 0) : d113967 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15775 q = 0) : d123728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
  have h7 (q : Pattern) (selected : d10371 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15776 q = 0) : d123729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10373 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15777 q = 0) : d123730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d123730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15777, d123730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214370 q = 0) : d215992 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214370, d215992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214370, d215992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d214374 q = 0) : d215996 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214374, d215996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d214374, d215996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d214375 q = 0) : d215997 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214375, d215997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214375, d215997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro21017 (p : Pattern) (selected : d214380 p = 0) : d216002 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2340 q = 0) : d53505 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro558 q selected
  have h2 (q : Pattern) (selected : d2053 q = 0) : d53332 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro558 q selected
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2341 q = 0) : d53506 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2054 q = 0) : d53333 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2342 q = 0) : d53507 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17391 q = 0) : d128053 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17391, d128053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17391, d128053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6762 q selected
  have h7 (q : Pattern) (selected : d10391 q = 0) : d101712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6762 q selected
    | true =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17392 q = 0) : d128054 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17392, d128054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17392, d128054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10393 q = 0) : d101714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10393, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10393, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17393 q = 0) : d128055 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17393, d128055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17393, d128055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214379 q = 0) : d216001 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214379, d216001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214379, d216001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15775 q = 0) : d123728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
  have h13 (q : Pattern) (selected : d10371 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15776 q = 0) : d123729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10373 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d15777 q = 0) : d123730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d123730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d15777, d123730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d214374 q = 0) : d215996 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214374, d215996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d214374, d215996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d214380 q = 0) : d216002 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214380, d216002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214380, d216002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro21018 (p : Pattern) (selected : d214385 p = 0) : d216007 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d6643 q = 0) : d76361 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6643, d76361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6643, d76361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2828 q selected
  have h2 (q : Pattern) (selected : d5247 q = 0) : d69331 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2828 q selected
    | true =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6644 q = 0) : d76362 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6644, d76362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6644, d76362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5248 q = 0) : d69332 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, d69332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d5248, d69332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6645 q = 0) : d76363 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6645, d76363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6645, d76363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214383 q = 0) : d216005 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214383, d216005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214383, d216005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15790 q = 0) : d123743 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6764 q selected
  have h8 (q : Pattern) (selected : d10412 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6764 q selected
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15791 q = 0) : d123744 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10414 q = 0) : d101735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15792 q = 0) : d123745 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d214384 q = 0) : d216006 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214384, d216006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214384, d216006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d214385 q = 0) : d216007 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214385, d216007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214385, d216007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro21019 (p : Pattern) (selected : d214390 p = 0) : d216012 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214372 q = 0) : d215994 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214372, d215994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21014 q selected
    | true =>
      simp only [d214372, d215994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21015 q selected
  have h2 (q : Pattern) (selected : d214373 q = 0) : d215995 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214373, d215995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214373, d215995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214376 q = 0) : d215998 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214376, d215998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21015 q selected
    | true =>
      simp only [d214376, d215998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21016 q selected
  have h4 (q : Pattern) (selected : d214377 q = 0) : d215999 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214377, d215999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214377, d215999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214378 q = 0) : d216000 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214378, d216000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214378, d216000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214381 q = 0) : d216003 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214381, d216003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21015 q selected
    | true =>
      simp only [d214381, d216003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21017 q selected
  have h7 (q : Pattern) (selected : d214382 q = 0) : d216004 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214382, d216004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214382, d216004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214386 q = 0) : d216008 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214386, d216008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21017 q selected
    | true =>
      simp only [d214386, d216008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21018 q selected
  have h9 (q : Pattern) (selected : d214387 q = 0) : d216009 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214387, d216009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214387, d216009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214388 q = 0) : d216010 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214388, d216010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214388, d216010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214389 q = 0) : d216011 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214389, d216011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214389, d216011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d214390 q = 0) : d216012 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214390, d216012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214390, d216012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro21020 (p : Pattern) (selected : d214395 p = 0) : d216017 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214381 q = 0) : d216003 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214381, d216003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21015 q selected
    | true =>
      simp only [d214381, d216003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21017 q selected
  have h2 (q : Pattern) (selected : d214382 q = 0) : d216004 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214382, d216004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214382, d216004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214386 q = 0) : d216008 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214386, d216008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21017 q selected
    | true =>
      simp only [d214386, d216008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21018 q selected
  have h4 (q : Pattern) (selected : d214387 q = 0) : d216009 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214387, d216009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214387, d216009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214388 q = 0) : d216010 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214388, d216010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214388, d216010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214393 q = 0) : d216015 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214393, d216015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214393, d216015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214394 q = 0) : d216016 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214394, d216016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214394, d216016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214395 q = 0) : d216017 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214395, d216017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214395, d216017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21021 (p : Pattern) (selected : d214401 p = 0) : d216023 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214391 q = 0) : d216013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214391, d216013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21019 q selected
    | true =>
      simp only [d214391, d216013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214392 q = 0) : d216014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214392, d216014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214392, d216014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214396 q = 0) : d216018 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214396, d216018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21020 q selected
    | true =>
      simp only [d214396, d216018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214397 q = 0) : d216019 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214397, d216019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214397, d216019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214398 q = 0) : d216020 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214398, d216020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214398, d216020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214399 q = 0) : d216021 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214399, d216021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214399, d216021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214400 q = 0) : d216022 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214400, d216022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214400, d216022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214401 q = 0) : d216023 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214401, d216023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214401, d216023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21022 (p : Pattern) (selected : d214403 p = 0) : d216025 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2346 q = 0) : d53511 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
  have h2 (q : Pattern) (selected : d2065 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2347 q = 0) : d53512 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2066 q = 0) : d53345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2348 q = 0) : d53513 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214402 q = 0) : d216024 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214402, d216024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214402, d216024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15790 q = 0) : d123743 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6764 q selected
  have h8 (q : Pattern) (selected : d10412 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6764 q selected
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15791 q = 0) : d123744 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10414 q = 0) : d101735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15792 q = 0) : d123745 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d214384 q = 0) : d216006 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214384, d216006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214384, d216006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d214403 q = 0) : d216025 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214403, d216025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214403, d216025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro21023 (p : Pattern) (selected : d214408 p = 0) : d216030 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214404 q = 0) : d216026 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214404, d216026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21017 q selected
    | true =>
      simp only [d214404, d216026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21022 q selected
  have h2 (q : Pattern) (selected : d214405 q = 0) : d216027 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214405, d216027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214405, d216027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214406 q = 0) : d216028 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214406, d216028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214406, d216028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214407 q = 0) : d216029 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214407, d216029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214407, d216029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214408 q = 0) : d216030 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214408, d216030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214408, d216030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21024 (p : Pattern) (selected : d214414 p = 0) : d216036 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214396 q = 0) : d216018 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214396, d216018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21020 q selected
    | true =>
      simp only [d214396, d216018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214397 q = 0) : d216019 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214397, d216019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214397, d216019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214409 q = 0) : d216031 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214409, d216031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21023 q selected
    | true =>
      simp only [d214409, d216031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214410 q = 0) : d216032 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214410, d216032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214410, d216032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214411 q = 0) : d216033 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214411, d216033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214411, d216033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214412 q = 0) : d216034 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214412, d216034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214412, d216034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214413 q = 0) : d216035 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214413, d216035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214413, d216035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214414 q = 0) : d216036 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214414, d216036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214414, d216036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21025 (p : Pattern) (selected : d214418 p = 0) : d215993 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2393 q = 0) : d53500 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2393, d53500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2393, d53500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro587 q selected
  have h2 (q : Pattern) (selected : d2201 q = 0) : d53314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2201, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro587 q selected
    | true =>
      simp only [d2201, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2394 q = 0) : d53501 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2394, d53501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2394, d53501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2202 q = 0) : d53315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2202, d53315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2202, d53315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2395 q = 0) : d53502 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2395, d53502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2395, d53502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17430 q = 0) : d128038 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17430, d128038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17430, d128038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6772 q selected
  have h7 (q : Pattern) (selected : d10458 q = 0) : d101685 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10458, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6772 q selected
    | true =>
      simp only [d10458, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17431 q = 0) : d128039 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17431, d128039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17431, d128039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10460 q = 0) : d101687 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10460, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10460, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17432 q = 0) : d128040 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17432, d128040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17432, d128040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214416 q = 0) : d215991 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214416, d215991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214416, d215991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15828 q = 0) : d113965 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15828, d113965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15828, d113965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6773 q selected
  have h13 (q : Pattern) (selected : d10468 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10468, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6773 q selected
    | true =>
      simp only [d10468, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15829 q = 0) : d113966 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15829, d113966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15829, d113966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10470 q = 0) : d101676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10470, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10470, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d15830 q = 0) : d113967 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15830, d113967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d15830, d113967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d15835 q = 0) : d123728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15835, d123728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15835, d123728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
  have h18 (q : Pattern) (selected : d10482 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
    | true =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d15836 q = 0) : d123729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15836, d123729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15836, d123729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10484 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d15837 q = 0) : d123730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15837, d123730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d15837, d123730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d214417 q = 0) : d215992 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214417, d215992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d214417, d215992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d214418 q = 0) : d215993 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214418, d215993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214418, d215993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro21026 (p : Pattern) (selected : d214421 p = 0) : d216002 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2397 q = 0) : d53505 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2397, d53505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2397, d53505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro592 q selected
  have h2 (q : Pattern) (selected : d2219 q = 0) : d53332 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro592 q selected
    | true =>
      simp only [d2219, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2398 q = 0) : d53506 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2398, d53506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2398, d53506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2220 q = 0) : d53333 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2220, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2220, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2399 q = 0) : d53507 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2399, d53507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2399, d53507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17437 q = 0) : d128053 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17437, d128053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17437, d128053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6776 q selected
  have h7 (q : Pattern) (selected : d10493 q = 0) : d101712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10493, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6776 q selected
    | true =>
      simp only [d10493, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17438 q = 0) : d128054 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17438, d128054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17438, d128054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10495 q = 0) : d101714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10495, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10495, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17439 q = 0) : d128055 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17439, d128055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17439, d128055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214419 q = 0) : d216001 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214419, d216001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214419, d216001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15835 q = 0) : d123728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15835, d123728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15835, d123728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
  have h13 (q : Pattern) (selected : d10482 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
    | true =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15836 q = 0) : d123729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15836, d123729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15836, d123729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10484 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d15837 q = 0) : d123730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15837, d123730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d15837, d123730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d214420 q = 0) : d215996 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214420, d215996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d214420, d215996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d214421 q = 0) : d216002 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214421, d216002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214421, d216002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro21027 (p : Pattern) (selected : d214426 p = 0) : d216007 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13862 q = 0) : d76361 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13862, d76361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13862, d76361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6778 q selected
  have h2 (q : Pattern) (selected : d10508 q = 0) : d69331 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10508, d69331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6778 q selected
    | true =>
      simp only [d10508, d69331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13863 q = 0) : d76362 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13863, d76362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13863, d76362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10510 q = 0) : d69332 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10510, d69332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10510, d69332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13864 q = 0) : d76363 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13864, d76363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13864, d76363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214424 q = 0) : d216005 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214424, d216005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214424, d216005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15844 q = 0) : d123743 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15844, d123743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15844, d123743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6779 q selected
  have h8 (q : Pattern) (selected : d10521 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6779 q selected
    | true =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15845 q = 0) : d123744 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15845, d123744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15845, d123744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10523 q = 0) : d101735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10523, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10523, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15846 q = 0) : d123745 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15846, d123745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15846, d123745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d214425 q = 0) : d216006 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214425, d216006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214425, d216006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d214426 q = 0) : d216007 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214426, d216007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214426, d216007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro21028 (p : Pattern) (selected : d214431 p = 0) : d216025 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2402 q = 0) : d53511 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2402, d53511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2402, d53511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro593 q selected
  have h2 (q : Pattern) (selected : d2231 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro593 q selected
    | true =>
      simp only [d2231, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2403 q = 0) : d53512 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2403, d53512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2403, d53512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2232 q = 0) : d53345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2232, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2404 q = 0) : d53513 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2404, d53513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2404, d53513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214430 q = 0) : d216024 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214430, d216024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214430, d216024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15844 q = 0) : d123743 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15844, d123743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15844, d123743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6779 q selected
  have h8 (q : Pattern) (selected : d10521 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6779 q selected
    | true =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15845 q = 0) : d123744 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15845, d123744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15845, d123744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10523 q = 0) : d101735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10523, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10523, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15846 q = 0) : d123745 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15846, d123745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15846, d123745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d214425 q = 0) : d216006 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214425, d216006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214425, d216006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d214431 q = 0) : d216025 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214431, d216025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214431, d216025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro21029 (p : Pattern) (selected : d214436 p = 0) : d216039 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214422 q = 0) : d216003 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214422, d216003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21025 q selected
    | true =>
      simp only [d214422, d216003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21026 q selected
  have h2 (q : Pattern) (selected : d214423 q = 0) : d216004 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214423, d216004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214423, d216004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214427 q = 0) : d216008 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214427, d216008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21026 q selected
    | true =>
      simp only [d214427, d216008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21027 q selected
  have h4 (q : Pattern) (selected : d214428 q = 0) : d216009 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214428, d216009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214428, d216009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214429 q = 0) : d216010 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214429, d216010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214429, d216010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214432 q = 0) : d216026 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214432, d216026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21026 q selected
    | true =>
      simp only [d214432, d216026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21028 q selected
  have h7 (q : Pattern) (selected : d214433 q = 0) : d216027 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214433, d216027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214433, d216027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214434 q = 0) : d216028 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214434, d216028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214434, d216028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214435 q = 0) : d216038 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214435, d216038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214435, d216038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214436 q = 0) : d216039 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214436, d216039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d214436, d216039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21030 (p : Pattern) (selected : d214440 p = 0) : d216030 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214432 q = 0) : d216026 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214432, d216026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21026 q selected
    | true =>
      simp only [d214432, d216026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21028 q selected
  have h2 (q : Pattern) (selected : d214433 q = 0) : d216027 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214433, d216027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214433, d216027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214434 q = 0) : d216028 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214434, d216028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214434, d216028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214439 q = 0) : d216029 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214439, d216029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214439, d216029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214440 q = 0) : d216030 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214440, d216030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214440, d216030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21031 (p : Pattern) (selected : d214446 p = 0) : d216045 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214437 q = 0) : d216040 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214437, d216040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21029 q selected
    | true =>
      simp only [d214437, d216040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214438 q = 0) : d216041 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214438, d216041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214438, d216041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214441 q = 0) : d216031 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214441, d216031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21030 q selected
    | true =>
      simp only [d214441, d216031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214442 q = 0) : d216032 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214442, d216032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214442, d216032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214443 q = 0) : d216042 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214443, d216042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214443, d216042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214444 q = 0) : d216043 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214444, d216043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214444, d216043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214445 q = 0) : d216044 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214445, d216044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214445, d216044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214446 q = 0) : d216045 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214446, d216045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214446, d216045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21032 (p : Pattern) (selected : d214450 p = 0) : d216049 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214441 q = 0) : d216031 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214441, d216031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21030 q selected
    | true =>
      simp only [d214441, d216031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214442 q = 0) : d216032 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214442, d216032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214442, d216032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214447 q = 0) : d216046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214447, d216046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214447, d216046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214448 q = 0) : d216047 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214448, d216047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214448, d216047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214449 q = 0) : d216048 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214449, d216048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214449, d216048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214450 q = 0) : d216049 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214450, d216049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214450, d216049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21033 (p : Pattern) (selected : d214453 p = 0) : d216052 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2346 q = 0) : d53511 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
  have h2 (q : Pattern) (selected : d2065 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2347 q = 0) : d53512 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2066 q = 0) : d53345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2348 q = 0) : d53513 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214402 q = 0) : d216024 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214402, d216024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214402, d216024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214453 q = 0) : d216052 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214453, d216052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214453, d216052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro21034 (p : Pattern) (selected : d214458 p = 0) : d216057 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214381 q = 0) : d216003 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214381, d216003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21015 q selected
    | true =>
      simp only [d214381, d216003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21017 q selected
  have h2 (q : Pattern) (selected : d214382 q = 0) : d216004 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214382, d216004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214382, d216004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214386 q = 0) : d216008 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214386, d216008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21017 q selected
    | true =>
      simp only [d214386, d216008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21018 q selected
  have h4 (q : Pattern) (selected : d214387 q = 0) : d216009 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214387, d216009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214387, d216009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214388 q = 0) : d216010 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214388, d216010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214388, d216010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214454 q = 0) : d216053 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214454, d216053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21017 q selected
    | true =>
      simp only [d214454, d216053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21033 q selected
  have h7 (q : Pattern) (selected : d214455 q = 0) : d216054 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214455, d216054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214455, d216054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214456 q = 0) : d216055 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214456, d216055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214456, d216055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214457 q = 0) : d216056 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214457, d216056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214457, d216056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214458 q = 0) : d216057 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214458, d216057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d214458, d216057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21035 (p : Pattern) (selected : d214464 p = 0) : d216063 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214459 q = 0) : d216058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214459, d216058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21034 q selected
    | true =>
      simp only [d214459, d216058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214460 q = 0) : d216059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214460, d216059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214460, d216059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214461 q = 0) : d216060 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214461, d216060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214461, d216060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214462 q = 0) : d216061 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214462, d216061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214462, d216061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214463 q = 0) : d216062 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214463, d216062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214463, d216062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214464 q = 0) : d216063 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214464, d216063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214464, d216063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21036 (p : Pattern) (selected : d214470 p = 0) : d216069 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214415 q = 0) : d216037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214415, d216037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21021 q selected
    | true =>
      simp only [d214415, d216037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21024 q selected
  have h2 (q : Pattern) (selected : d214451 q = 0) : d216050 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214451, d216050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21031 q selected
    | true =>
      simp only [d214451, d216050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21032 q selected
  have h3 (q : Pattern) (selected : d214452 q = 0) : d216051 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214452, d216051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214452, d216051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d214465 q = 0) : d216064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214465, d216064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21035 q selected
    | true =>
      simp only [d214465, d216064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214466 q = 0) : d216065 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214466, d216065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214466, d216065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214467 q = 0) : d216066 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214467, d216066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214467, d216066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214468 q = 0) : d216067 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214468, d216067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214468, d216067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214469 q = 0) : d216068 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214469, d216068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214469, d216068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d214470 q = 0) : d216069 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214470, d216069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214470, d216069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21037 (p : Pattern) (selected : d214475 p = 0) : d216049 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214409 q = 0) : d216031 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214409, d216031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21023 q selected
    | true =>
      simp only [d214409, d216031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214410 q = 0) : d216032 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214410, d216032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214410, d216032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214472 q = 0) : d216046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214472, d216046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214472, d216046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214473 q = 0) : d216047 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214473, d216047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214473, d216047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214474 q = 0) : d216048 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214474, d216048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214474, d216048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214475 q = 0) : d216049 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214475, d216049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214475, d216049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21038 (p : Pattern) (selected : d214481 p = 0) : d216076 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214476 q = 0) : d216071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214476, d216071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21037 q selected
    | true =>
      simp only [d214476, d216071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214477 q = 0) : d216072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214477, d216072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214477, d216072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214478 q = 0) : d216073 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214478, d216073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214478, d216073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214479 q = 0) : d216074 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214479, d216074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214479, d216074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214480 q = 0) : d216075 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214480, d216075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214480, d216075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214481 q = 0) : d216076 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214481, d216076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214481, d216076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21039 (p : Pattern) (selected : d214487 p = 0) : d216082 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214197 q = 0) : d215858 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214197, d215858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214197, d215858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20974 q selected
  have h2 (q : Pattern) (selected : d214198 q = 0) : d215859 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d214198, d215859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214198, d215859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d214207 q = 0) : d215868 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214207, d215868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20974 q selected
    | true =>
      simp only [d214207, d215868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20977 q selected
  have h4 (q : Pattern) (selected : d214208 q = 0) : d215869 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d214208, d215869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214208, d215869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214209 q = 0) : d215870 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d214209, d215870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214209, d215870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214334 q = 0) : d215956 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214334, d215956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20999 q selected
    | true =>
      simp only [d214334, d215956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21009 q selected
  have h7 (q : Pattern) (selected : d214352 q = 0) : d215974 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214352, d215974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21010 q selected
    | true =>
      simp only [d214352, d215974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21011 q selected
  have h8 (q : Pattern) (selected : d214353 q = 0) : d215975 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d214353, d215975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214353, d215975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d214354 q = 0) : d215976 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d214354, d215976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d214354, d215976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d214355 q = 0) : d215977 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d214355, d215977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214355, d215977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214359 q = 0) : d215981 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214359, d215981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214359, d215981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21012 q selected
  have h12 (q : Pattern) (selected : d214361 q = 0) : d215983 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214361, d215983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214361, d215983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21013 q selected
  have h13 (q : Pattern) (selected : d214362 q = 0) : d215984 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d214362, d215984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214362, d215984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d214363 q = 0) : d215985 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d214363, d215985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d214363, d215985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d214364 q = 0) : d215986 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d214364, d215986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d214364, d215986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d214365 q = 0) : d215987 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d214365, d215987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d214365, d215987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d214471 q = 0) : d216070 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214471, d216070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214471, d216070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21036 q selected
  have h18 (q : Pattern) (selected : d214482 q = 0) : d216077 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214482, d216077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214482, d216077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21038 q selected
  have h19 (q : Pattern) (selected : d214483 q = 0) : d216078 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d214483, d216078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d214483, d216078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d214484 q = 0) : d216079 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d214484, d216079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d214484, d216079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d214485 q = 0) : d216080 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d214485, d216080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d214485, d216080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d214486 q = 0) : d216081 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d214486, d216081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d214486, d216081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d214487 q = 0) : d216082 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d214487, d216082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d214487, d216082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro21040 (p : Pattern) (selected : d214493 p = 0) : d216088 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214488 q = 0) : d216083 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d214488, d216083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214488, d216083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21039 q selected
  have h2 (q : Pattern) (selected : d214489 q = 0) : d216084 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d214489, d216084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214489, d216084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214490 q = 0) : d216085 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d214490, d216085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214490, d216085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d214491 q = 0) : d216086 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d214491, d216086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214491, d216086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214492 q = 0) : d216087 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d214492, d216087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214492, d216087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214493 q = 0) : d216088 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d214493, d216088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214493, d216088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21041 (p : Pattern) (selected : d214499 p = 0) : d216094 p = 1 := by
  have h0 (q : Pattern) (selected : d213186 q = 0) : d215041 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d213186, d215041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20697 q selected
    | true =>
      simp only [d213186, d215041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20751 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d213467 q = 0) : d215260 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d213467, d215260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213467, d215260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20815 q selected
  have h3 (q : Pattern) (selected : d213468 q = 0) : d215261 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d213468, d215261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213468, d215261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213809 q = 0) : d215536 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d213809, d215536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213809, d215536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20890 q selected
  have h5 (q : Pattern) (selected : d213810 q = 0) : d215537 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d213810, d215537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213810, d215537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213811 q = 0) : d215538 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d213811, d215538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213811, d215538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214152 q = 0) : d215813 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d214152, d215813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214152, d215813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20965 q selected
  have h8 (q : Pattern) (selected : d214153 q = 0) : d215814 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d214153, d215814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214153, d215814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d214154 q = 0) : d215815 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d214154, d215815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214154, d215815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214155 q = 0) : d215816 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d214155, d215816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214155, d215816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214494 q = 0) : d216089 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d214494, d216089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214494, d216089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21040 q selected
  have h12 (q : Pattern) (selected : d214495 q = 0) : d216090 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d214495, d216090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214495, d216090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d214496 q = 0) : d216091 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d214496, d216091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214496, d216091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d214497 q = 0) : d216092 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d214497, d216092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214497, d216092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d214498 q = 0) : d216093 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d214498, d216093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d214498, d216093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d214499 q = 0) : d216094 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d214499, d216094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d214499, d216094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro21042 (p : Pattern) (selected : d214505 p = 0) : d216100 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214500 q = 0) : d216095 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d214500, d216095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21041 q selected
    | true =>
      simp only [d214500, d216095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214501 q = 0) : d216096 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d214501, d216096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214501, d216096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d214502 q = 0) : d216097 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d214502, d216097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214502, d216097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214503 q = 0) : d216098 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d214503, d216098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214503, d216098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214504 q = 0) : d216099 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d214504, d216099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214504, d216099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214505 q = 0) : d216100 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d214505, d216100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214505, d216100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21043 (p : Pattern) (selected : d214511 p = 0) : d216106 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214506 q = 0) : d216101 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d214506, d216101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21042 q selected
    | true =>
      simp only [d214506, d216101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214507 q = 0) : d216102 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d214507, d216102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214507, d216102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d214508 q = 0) : d216103 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d214508, d216103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214508, d216103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214509 q = 0) : d216104 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d214509, d216104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214509, d216104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214510 q = 0) : d216105 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d214510, d216105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214510, d216105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214511 q = 0) : d216106 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d214511, d216106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214511, d216106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21044 (p : Pattern) (selected : d214517 p = 0) : d216112 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214512 q = 0) : d216107 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d214512, d216107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21043 q selected
    | true =>
      simp only [d214512, d216107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214513 q = 0) : d216108 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d214513, d216108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214513, d216108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d214514 q = 0) : d216109 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d214514, d216109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214514, d216109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214515 q = 0) : d216110 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d214515, d216110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214515, d216110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214516 q = 0) : d216111 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d214516, d216111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214516, d216111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214517 q = 0) : d216112 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d214517, d216112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214517, d216112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21045 (p : Pattern) (selected : d214523 p = 0) : d216118 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214518 q = 0) : d216113 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d214518, d216113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21044 q selected
    | true =>
      simp only [d214518, d216113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214519 q = 0) : d216114 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d214519, d216114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214519, d216114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d214520 q = 0) : d216115 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d214520, d216115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214520, d216115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214521 q = 0) : d216116 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d214521, d216116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214521, d216116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214522 q = 0) : d216117 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d214522, d216117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214522, d216117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214523 q = 0) : d216118 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d214523, d216118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214523, d216118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21046 (p : Pattern) (selected : d214529 p = 0) : d216124 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214524 q = 0) : d216119 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d214524, d216119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21045 q selected
    | true =>
      simp only [d214524, d216119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214525 q = 0) : d216120 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d214525, d216120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214525, d216120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d214526 q = 0) : d216121 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d214526, d216121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214526, d216121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214527 q = 0) : d216122 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d214527, d216122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214527, d216122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214528 q = 0) : d216123 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d214528, d216123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214528, d216123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214529 q = 0) : d216124 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d214529, d216124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214529, d216124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21047 (p : Pattern) (selected : d214535 p = 0) : d216130 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214530 q = 0) : d216125 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d214530, d216125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21046 q selected
    | true =>
      simp only [d214530, d216125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214531 q = 0) : d216126 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d214531, d216126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214531, d216126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d214532 q = 0) : d216127 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d214532, d216127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214532, d216127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214533 q = 0) : d216128 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d214533, d216128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214533, d216128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214534 q = 0) : d216129 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d214534, d216129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214534, d216129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214535 q = 0) : d216130 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d214535, d216130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214535, d216130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21048 (p : Pattern) (selected : d214541 p = 0) : d216136 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214536 q = 0) : d216131 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d214536, d216131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21047 q selected
    | true =>
      simp only [d214536, d216131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214537 q = 0) : d216132 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d214537, d216132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214537, d216132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d214538 q = 0) : d216133 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d214538, d216133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214538, d216133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214539 q = 0) : d216134 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d214539, d216134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214539, d216134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214540 q = 0) : d216135 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d214540, d216135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214540, d216135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214541 q = 0) : d216136 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d214541, d216136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214541, d216136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21049 (p : Pattern) (selected : d212684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d212683 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d212683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d212683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d212684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d212684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d212684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21050 (p : Pattern) (selected : d212689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212685 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d212685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21049 q selected
    | true =>
      simp only [d212685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d212686 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d212686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d212687 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d212687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d212687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d212688 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d212688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d212688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d212689 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d212689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d212689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21051 (p : Pattern) (selected : d212695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212690 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d212690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21050 q selected
    | true =>
      simp only [d212690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d212691 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d212691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d212692 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d212692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d212692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d212693 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d212693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d212693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d212694 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d212694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d212694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d212695 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d212695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21052 (p : Pattern) (selected : d212701 p = 1) : d216141 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212662 q = 1) : d212662 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d212668 q = 1) : d212668 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d212682 q = 1) : d212682 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d212696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d212696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21051 q selected
    | true =>
      simp only [d212696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d212697 q = 1) : d216137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212697, d216137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d212697, d216137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d212591 q = 1) : d212591 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d212698 q = 1) : d216138 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212698, d216138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d212698, d216138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d212699 q = 1) : d216139 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212699, d216139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d212699, d216139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d212700 q = 1) : d216140 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212700, d216140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212700, d216140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d212701 q = 1) : d216141 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212701, d216141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212701, d216141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro21053 (p : Pattern) (selected : d212713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212690 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d212690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21050 q selected
    | true =>
      simp only [d212690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d212691 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d212691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d212692 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d212692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d212692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d212693 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d212693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d212693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d212694 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d212694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d212694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d212713 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d212713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d212713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21054 (p : Pattern) (selected : d212719 p = 1) : d216146 p = 1 := by
  have h0 (q : Pattern) (selected : d212662 q = 1) : d212662 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212668 q = 1) : d212668 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d212682 q = 1) : d212682 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d212696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d212696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21051 q selected
    | true =>
      simp only [d212696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d212697 q = 1) : d216137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212697, d216137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d212697, d216137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d212591 q = 1) : d212591 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d212698 q = 1) : d216138 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212698, d216138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d212698, d216138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d212699 q = 1) : d216139 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212699, d216139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212699, d216139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d212700 q = 1) : d216140 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212700, d216140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212700, d216140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d212706 q = 1) : d212706 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d212710 q = 1) : d212710 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d212712 q = 1) : d212712 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d212714 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d212714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21053 q selected
    | true =>
      simp only [d212714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d212715 q = 1) : d216142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212715, d216142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d212715, d216142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d212598 q = 1) : d212598 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d212716 q = 1) : d216143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212716, d216143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d212716, d216143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d212717 q = 1) : d216144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212717, d216144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d212717, d216144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d212718 q = 1) : d216145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212718, d216145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d212718, d216145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d212719 q = 1) : d216146 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212719, d216146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d212719, d216146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro21055 (p : Pattern) (selected : d212728 p = 1) : d216153 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212712 q = 1) : d212712 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d212714 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d212714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21053 q selected
    | true =>
      simp only [d212714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d212715 q = 1) : d216142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212715, d216142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212715, d216142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d212598 q = 1) : d212598 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d212716 q = 1) : d216143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212716, d216143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d212716, d216143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d212726 q = 1) : d216151 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212726, d216151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212726, d216151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d212727 q = 1) : d216152 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212727, d216152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212727, d216152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d212728 q = 1) : d216153 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212728, d216153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212728, d216153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21056 (p : Pattern) (selected : d212749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
  have h2 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d212748 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d212748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d212748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d212749 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d212749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d212749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro21057 (p : Pattern) (selected : d212754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212750 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d212750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21056 q selected
    | true =>
      simp only [d212750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d212751 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d212751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d212752 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d212752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d212752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d212753 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d212753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d212753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d212754 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d212754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d212754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21058 (p : Pattern) (selected : d212760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d212755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21057 q selected
    | true =>
      simp only [d212755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d212756 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d212756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d212757 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d212757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d212757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d212758 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d212758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d212758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d212759 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d212759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d212759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d212760 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d212760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d212760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21059 (p : Pattern) (selected : d212766 p = 1) : d216163 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212747 q = 1) : d212747 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d212761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d212761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21058 q selected
    | true =>
      simp only [d212761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d212762 q = 1) : d216159 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212762, d216159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212762, d216159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d212627 q = 1) : d212627 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d212763 q = 1) : d216160 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212763, d216160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d212763, d216160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d212764 q = 1) : d216161 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212764, d216161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212764, d216161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d212765 q = 1) : d216162 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212765, d216162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212765, d216162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d212766 q = 1) : d216163 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212766, d216163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212766, d216163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21060 (p : Pattern) (selected : d212772 p = 1) : d216169 p = 1 := by
  have h0 (q : Pattern) (selected : d212656 q = 1) : d212656 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212720 q = 1) : d216147 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212720, d216147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21052 q selected
    | true =>
      simp only [d212720, d216147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21054 q selected
  have h2 (q : Pattern) (selected : d212722 q = 1) : d212722 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d212723 q = 1) : d216148 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212723, d216148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212723, d216148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d212724 q = 1) : d216149 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212724, d216149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d212724, d216149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d212725 q = 1) : d216150 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212725, d216150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212725, d216150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d212729 q = 1) : d216154 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212729, d216154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d212729, d216154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21055 q selected
  have h8 (q : Pattern) (selected : d212730 q = 1) : d216155 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212730, d216155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d212730, d216155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d212731 q = 1) : d216156 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212731, d216156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d212731, d216156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d212732 q = 1) : d216157 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212732, d216157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d212732, d216157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d212733 q = 1) : d216158 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212733, d216158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d212733, d216158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d212767 q = 1) : d216164 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212767, d216164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d212767, d216164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21059 q selected
  have h13 (q : Pattern) (selected : d212768 q = 1) : d216165 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212768, d216165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d212768, d216165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d212769 q = 1) : d216166 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212769, d216166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d212769, d216166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d212770 q = 1) : d216167 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212770, d216167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d212770, d216167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d212771 q = 1) : d216168 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212771, d216168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d212771, d216168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d212772 q = 1) : d216169 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d212772, d216169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d212772, d216169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro21061 (p : Pattern) (selected : d212821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d350 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
    | true =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d212820 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d212820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d212820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d212683 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d212683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d212683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d212821 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d212821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d212821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21062 (p : Pattern) (selected : d212826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212822 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d212822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21061 q selected
    | true =>
      simp only [d212822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21049 q selected
  have h2 (q : Pattern) (selected : d212823 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d212823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d212685 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d212685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21049 q selected
    | true =>
      simp only [d212685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d212686 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d212686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d212824 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d212824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d212824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d212687 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d212687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d212687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d212825 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d212825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d212825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d212826 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d212826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d212826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21063 (p : Pattern) (selected : d212832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212827 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d212827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21062 q selected
    | true =>
      simp only [d212827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d212828 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d212828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d212690 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d212690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21050 q selected
    | true =>
      simp only [d212690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d212691 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d212691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d212829 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d212829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d212829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d212830 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d212830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d212830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d212831 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d212831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d212831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d212832 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d212832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21064 (p : Pattern) (selected : d212844 p = 1) : d216179 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212798 q = 1) : d212798 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d212804 q = 1) : d212804 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d212819 q = 1) : d212819 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d212833 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d212833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21063 q selected
    | true =>
      simp only [d212833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21051 q selected
  have h5 (q : Pattern) (selected : d212834 q = 1) : d216175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212834, d216175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d212834, d216175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d212840 q = 1) : d212840 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d212841 q = 1) : d216176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212841, d216176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d212841, d216176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d212842 q = 1) : d216177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212842, d216177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d212842, d216177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d212843 q = 1) : d216178 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212843, d216178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212843, d216178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d212844 q = 1) : d216179 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212844, d216179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212844, d216179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro21065 (p : Pattern) (selected : d212856 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212827 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d212827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21062 q selected
    | true =>
      simp only [d212827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d212828 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d212828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d212690 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d212690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21050 q selected
    | true =>
      simp only [d212690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d212691 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d212691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d212829 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d212829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d212829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d212830 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d212830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d212830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d212831 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d212831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d212831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d212856 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d212856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d212856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21066 (p : Pattern) (selected : d212865 p = 1) : d216184 p = 1 := by
  have h0 (q : Pattern) (selected : d212798 q = 1) : d212798 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212804 q = 1) : d212804 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d212819 q = 1) : d212819 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d212833 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d212833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21063 q selected
    | true =>
      simp only [d212833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21051 q selected
  have h4 (q : Pattern) (selected : d212834 q = 1) : d216175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212834, d216175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d212834, d216175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d212840 q = 1) : d212840 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d212841 q = 1) : d216176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212841, d216176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d212841, d216176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d212842 q = 1) : d216177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212842, d216177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212842, d216177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d212843 q = 1) : d216178 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212843, d216178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212843, d216178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d212849 q = 1) : d212849 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d212853 q = 1) : d212853 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d212855 q = 1) : d212855 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d212857 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d212857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21065 q selected
    | true =>
      simp only [d212857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21053 q selected
  have h13 (q : Pattern) (selected : d212858 q = 1) : d216180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212858, d216180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d212858, d216180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d212861 q = 1) : d212861 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d212862 q = 1) : d216181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212862, d216181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d212862, d216181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d212863 q = 1) : d216182 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212863, d216182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d212863, d216182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d212864 q = 1) : d216183 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212864, d216183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d212864, d216183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d212865 q = 1) : d216184 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212865, d216184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d212865, d216184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro21067 (p : Pattern) (selected : d212874 p = 1) : d216191 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212855 q = 1) : d212855 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d212857 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d212857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21065 q selected
    | true =>
      simp only [d212857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21053 q selected
  have h3 (q : Pattern) (selected : d212858 q = 1) : d216180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212858, d216180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212858, d216180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d212861 q = 1) : d212861 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d212862 q = 1) : d216181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212862, d216181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d212862, d216181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d212872 q = 1) : d216189 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212872, d216189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212872, d216189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d212873 q = 1) : d216190 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212873, d216190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212873, d216190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d212874 q = 1) : d216191 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212874, d216191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212874, d216191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21068 (p : Pattern) (selected : d212898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d431 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
  have h2 (q : Pattern) (selected : d350 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
    | true =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d432 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d433 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
  have h7 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d212897 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d212897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d212897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d212748 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d212748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d212748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d212898 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d212898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d212898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro21069 (p : Pattern) (selected : d212903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212899 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d212899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21068 q selected
    | true =>
      simp only [d212899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21056 q selected
  have h2 (q : Pattern) (selected : d212900 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d212900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d212750 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d212750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21056 q selected
    | true =>
      simp only [d212750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d212751 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d212751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d212901 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d212901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d212901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d212752 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d212752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d212752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d212902 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d212902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d212902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d212903 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d212903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d212903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21070 (p : Pattern) (selected : d212909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d212904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21069 q selected
    | true =>
      simp only [d212904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d212905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d212905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d212755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d212755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21057 q selected
    | true =>
      simp only [d212755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d212756 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d212756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d212906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d212906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d212906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d212907 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d212907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d212907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d212908 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d212908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d212908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d212909 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d212909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d212909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21071 (p : Pattern) (selected : d212921 p = 1) : d216201 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212896 q = 1) : d212896 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d212910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d212910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21070 q selected
    | true =>
      simp only [d212910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21058 q selected
  have h3 (q : Pattern) (selected : d212911 q = 1) : d216197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212911, d216197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212911, d216197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d212917 q = 1) : d212917 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d212918 q = 1) : d216198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212918, d216198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d212918, d216198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d212919 q = 1) : d216199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212919, d216199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212919, d216199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d212920 q = 1) : d216200 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212920, d216200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212920, d216200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d212921 q = 1) : d216201 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212921, d216201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212921, d216201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21072 (p : Pattern) (selected : d212933 p = 1) : d216207 p = 1 := by
  have h0 (q : Pattern) (selected : d212792 q = 1) : d212792 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212866 q = 1) : d216185 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212866, d216185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21064 q selected
    | true =>
      simp only [d212866, d216185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21066 q selected
  have h2 (q : Pattern) (selected : d212868 q = 1) : d212868 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d212869 q = 1) : d216186 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212869, d216186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212869, d216186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d212870 q = 1) : d216187 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212870, d216187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d212870, d216187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d212871 q = 1) : d216188 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212871, d216188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212871, d216188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d212875 q = 1) : d216192 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212875, d216192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d212875, d216192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21067 q selected
  have h8 (q : Pattern) (selected : d212877 q = 1) : d212877 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d212878 q = 1) : d216193 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212878, d216193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d212878, d216193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d212879 q = 1) : d216194 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212879, d216194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d212879, d216194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d212880 q = 1) : d216195 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212880, d216195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d212880, d216195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d212881 q = 1) : d216196 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212881, d216196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d212881, d216196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d212922 q = 1) : d216202 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212922, d216202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d212922, d216202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21071 q selected
  have h14 (q : Pattern) (selected : d212928 q = 1) : d212928 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d212929 q = 1) : d216203 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212929, d216203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d212929, d216203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d212930 q = 1) : d216204 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212930, d216204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d212930, d216204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d212931 q = 1) : d216205 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212931, d216205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d212931, d216205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d212932 q = 1) : d216206 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212932, d216206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d212932, d216206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d212933 q = 1) : d216207 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d212933, d216207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d212933, d216207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro21073 (p : Pattern) (selected : d212939 p = 1) : d216213 p = 1 := by
  have h0 (q : Pattern) (selected : d212641 q = 1) : d212641 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d212773 q = 1) : d216170 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d212773, d216170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212773, d216170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21060 q selected
  have h3 (q : Pattern) (selected : d212774 q = 1) : d216171 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d212774, d216171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212774, d216171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d212775 q = 1) : d216172 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d212775, d216172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212775, d216172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d212776 q = 1) : d216173 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d212776, d216173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212776, d216173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d212777 q = 1) : d216174 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d212777, d216174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212777, d216174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d212934 q = 1) : d216208 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d212934, d216208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212934, d216208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21072 q selected
  have h8 (q : Pattern) (selected : d212935 q = 1) : d216209 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d212935, d216209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212935, d216209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d212936 q = 1) : d216210 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d212936, d216210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212936, d216210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d212937 q = 1) : d216211 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d212937, d216211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212937, d216211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d212938 q = 1) : d216212 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d212938, d216212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212938, d216212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d212939 q = 1) : d216213 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d212939, d216213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d212939, d216213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro21074 (p : Pattern) (selected : d213013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d574 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
    | true =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d575 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d576 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d350 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
    | true =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213011 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6813 q selected
    | true =>
      simp only [d9512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14282 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d172 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213012 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d213013 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21075 (p : Pattern) (selected : d213019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213014 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21074 q selected
    | true =>
      simp only [d213014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21061 q selected
  have h2 (q : Pattern) (selected : d213015 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d212822 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d212822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21061 q selected
    | true =>
      simp only [d212822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21049 q selected
  have h4 (q : Pattern) (selected : d212823 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d212823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213016 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213017 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213018 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213019 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21076 (p : Pattern) (selected : d213023 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212822 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d212822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21061 q selected
    | true =>
      simp only [d212822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21049 q selected
  have h2 (q : Pattern) (selected : d212823 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d212823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213017 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213022 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213023 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21077 (p : Pattern) (selected : d213029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213020 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21075 q selected
    | true =>
      simp only [d213020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213021 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213024 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21076 q selected
    | true =>
      simp only [d213024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213025 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213026 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213027 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213028 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213029 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21078 (p : Pattern) (selected : d213033 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213024 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21076 q selected
    | true =>
      simp only [d213024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213025 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213030 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213031 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213032 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213033 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21079 (p : Pattern) (selected : d213045 p = 1) : d216218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212983 q = 1) : d212983 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d212992 q = 1) : d212992 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d213010 q = 1) : d213010 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d213034 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21077 q selected
    | true =>
      simp only [d213034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21078 q selected
  have h5 (q : Pattern) (selected : d213035 q = 1) : d216214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213035, d216214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213035, d216214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213041 q = 1) : d213041 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d213042 q = 1) : d216215 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213042, d216215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213042, d216215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213043 q = 1) : d216216 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213043, d216216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213043, d216216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d213044 q = 1) : d216217 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213044, d216217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213044, d216217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213045 q = 1) : d216218 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213045, d216218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213045, d216218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro21080 (p : Pattern) (selected : d213059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213020 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21075 q selected
    | true =>
      simp only [d213020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213021 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213024 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21076 q selected
    | true =>
      simp only [d213024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213025 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213026 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213027 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213028 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213059 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21081 (p : Pattern) (selected : d213060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213024 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21076 q selected
    | true =>
      simp only [d213024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213025 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213030 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213031 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213032 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213060 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21082 (p : Pattern) (selected : d213069 p = 1) : d216223 p = 1 := by
  have h0 (q : Pattern) (selected : d212983 q = 1) : d212983 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212992 q = 1) : d212992 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d213010 q = 1) : d213010 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d213034 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21077 q selected
    | true =>
      simp only [d213034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21078 q selected
  have h4 (q : Pattern) (selected : d213035 q = 1) : d216214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213035, d216214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213035, d216214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213041 q = 1) : d213041 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d213042 q = 1) : d216215 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213042, d216215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213042, d216215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213043 q = 1) : d216216 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213043, d216216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213043, d216216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213044 q = 1) : d216217 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213044, d216217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213044, d216217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d213051 q = 1) : d213051 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d213056 q = 1) : d213056 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d213058 q = 1) : d213058 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d213061 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21080 q selected
    | true =>
      simp only [d213061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21081 q selected
  have h13 (q : Pattern) (selected : d213062 q = 1) : d216219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213062, d216219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213062, d216219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213065 q = 1) : d213065 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d213066 q = 1) : d216220 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213066, d216220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d213066, d216220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d213067 q = 1) : d216221 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213067, d216221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213067, d216221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d213068 q = 1) : d216222 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213068, d216222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d213068, d216222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d213069 q = 1) : d216223 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213069, d216223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d213069, d216223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro21083 (p : Pattern) (selected : d213089 p = 1) : d216230 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213058 q = 1) : d213058 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d213061 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21080 q selected
    | true =>
      simp only [d213061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21081 q selected
  have h3 (q : Pattern) (selected : d213062 q = 1) : d216219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213062, d216219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213062, d216219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213065 q = 1) : d213065 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d213066 q = 1) : d216220 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213066, d216220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213066, d216220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213087 q = 1) : d216228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213087, d216228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213087, d216228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213088 q = 1) : d216229 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213088, d216229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213088, d216229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213089 q = 1) : d216230 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213089, d216230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213089, d216230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21084 (p : Pattern) (selected : d213130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
  have h2 (q : Pattern) (selected : d574 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
    | true =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d575 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d431 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
  have h7 (q : Pattern) (selected : d350 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
    | true =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d432 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d351 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d433 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213128 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d14404 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6813 q selected
  have h13 (q : Pattern) (selected : d9512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6813 q selected
    | true =>
      simp only [d9512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d14405 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d14405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d9514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d14406 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d14406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
  have h18 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d213129 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d213129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d213130 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro21085 (p : Pattern) (selected : d213136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213131 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21084 q selected
    | true =>
      simp only [d213131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21068 q selected
  have h2 (q : Pattern) (selected : d213132 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d212899 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d212899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21068 q selected
    | true =>
      simp only [d212899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21056 q selected
  have h4 (q : Pattern) (selected : d212900 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d212900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213133 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213134 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213135 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213136 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21086 (p : Pattern) (selected : d213140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212899 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d212899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21068 q selected
    | true =>
      simp only [d212899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21056 q selected
  have h2 (q : Pattern) (selected : d212900 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d212900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213134 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213139 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213140 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21087 (p : Pattern) (selected : d213146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213137 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21085 q selected
    | true =>
      simp only [d213137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213138 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21086 q selected
    | true =>
      simp only [d213141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213144 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213145 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213146 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21088 (p : Pattern) (selected : d213150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21086 q selected
    | true =>
      simp only [d213141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213147 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213148 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213149 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213150 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21089 (p : Pattern) (selected : d213162 p = 1) : d216240 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213127 q = 1) : d213127 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d213151 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21087 q selected
    | true =>
      simp only [d213151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21088 q selected
  have h3 (q : Pattern) (selected : d213152 q = 1) : d216236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213152, d216236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213152, d216236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213158 q = 1) : d213158 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d213159 q = 1) : d216237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213159, d216237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213159, d216237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213160 q = 1) : d216238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213160, d216238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213160, d216238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213161 q = 1) : d216239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213161, d216239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213161, d216239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213162 q = 1) : d216240 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213162, d216240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213162, d216240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21090 (p : Pattern) (selected : d213179 p = 1) : d216246 p = 1 := by
  have h0 (q : Pattern) (selected : d212975 q = 1) : d212975 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213070 q = 1) : d216224 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213070, d216224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21079 q selected
    | true =>
      simp only [d213070, d216224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21082 q selected
  have h2 (q : Pattern) (selected : d213083 q = 1) : d213083 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d213084 q = 1) : d216225 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213084, d216225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213084, d216225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d213085 q = 1) : d216226 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213085, d216226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213085, d216226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213086 q = 1) : d216227 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d213086, d216227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213086, d216227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213090 q = 1) : d216231 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213090, d216231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213090, d216231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21083 q selected
  have h8 (q : Pattern) (selected : d213092 q = 1) : d213092 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d213093 q = 1) : d216232 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213093, d216232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213093, d216232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213094 q = 1) : d216233 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213094, d216233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d213094, d216233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d213095 q = 1) : d216234 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d213095, d216234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213095, d216234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d213096 q = 1) : d216235 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d213096, d216235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213096, d216235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d213163 q = 1) : d216241 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213163, d216241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213163, d216241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21089 q selected
  have h14 (q : Pattern) (selected : d213174 q = 1) : d213174 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d213175 q = 1) : d216242 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213175, d216242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d213175, d216242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d213176 q = 1) : d216243 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213176, d216243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d213176, d216243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d213177 q = 1) : d216244 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d213177, d216244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d213177, d216244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d213178 q = 1) : d216245 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d213178, d216245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d213178, d216245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d213179 q = 1) : d216246 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d213179, d216246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d213179, d216246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro21091 (p : Pattern) (selected : d213185 p = 1) : d216252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213180 q = 1) : d216247 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d213180, d216247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213180, d216247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21090 q selected
  have h2 (q : Pattern) (selected : d213181 q = 1) : d216248 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d213181, d216248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213181, d216248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213182 q = 1) : d216249 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d213182, d216249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213182, d216249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213183 q = 1) : d216250 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d213183, d216250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213183, d216250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213184 q = 1) : d216251 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d213184, d216251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213184, d216251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213185 q = 1) : d216252 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d213185, d216252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213185, d216252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21092 (p : Pattern) (selected : d213271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro51 q selected
    | true =>
      simp only [d868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9661 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6823 q selected
    | true =>
      simp only [d9661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9663 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213269 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9671 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6824 q selected
    | true =>
      simp only [d9671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9673 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14551 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d875 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d876 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213270 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d213271 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21093 (p : Pattern) (selected : d213274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d574 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
    | true =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d575 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d576 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d875 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d876 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213272 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213273 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213274 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21094 (p : Pattern) (selected : d213277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d875 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d876 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213273 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213277 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21095 (p : Pattern) (selected : d213283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213275 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21092 q selected
    | true =>
      simp only [d213275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21093 q selected
  have h2 (q : Pattern) (selected : d213276 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213278 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21093 q selected
    | true =>
      simp only [d213278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21094 q selected
  have h4 (q : Pattern) (selected : d213279 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213280 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213281 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213282 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213283 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21096 (p : Pattern) (selected : d213287 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213278 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21093 q selected
    | true =>
      simp only [d213278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21094 q selected
  have h2 (q : Pattern) (selected : d213279 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213281 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213286 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213287 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21097 (p : Pattern) (selected : d213293 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21095 q selected
    | true =>
      simp only [d213284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213285 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213288 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21096 q selected
    | true =>
      simp only [d213288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213289 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213290 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213291 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213292 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213293 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21098 (p : Pattern) (selected : d213297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213288 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21096 q selected
    | true =>
      simp only [d213288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213289 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213294 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213295 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213296 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213297 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21099 (p : Pattern) (selected : d213309 p = 1) : d216258 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213241 q = 1) : d213241 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d213250 q = 1) : d213250 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d213268 q = 1) : d213268 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d213298 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21097 q selected
    | true =>
      simp only [d213298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21098 q selected
  have h5 (q : Pattern) (selected : d213299 q = 1) : d216254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213299, d216254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213299, d216254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213305 q = 1) : d213305 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d213306 q = 1) : d216255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213306, d216255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213306, d216255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213307 q = 1) : d216256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213307, d216256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213307, d216256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d213308 q = 1) : d216257 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213308, d216257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213308, d216257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213309 q = 1) : d216258 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213309, d216258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213309, d216258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro21100 (p : Pattern) (selected : d213323 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21095 q selected
    | true =>
      simp only [d213284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213285 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213288 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21096 q selected
    | true =>
      simp only [d213288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213289 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213290 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213291 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213292 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213323 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21101 (p : Pattern) (selected : d213324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213288 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21096 q selected
    | true =>
      simp only [d213288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213289 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213294 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213295 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213296 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213324 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21102 (p : Pattern) (selected : d213333 p = 1) : d216263 p = 1 := by
  have h0 (q : Pattern) (selected : d213241 q = 1) : d213241 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213250 q = 1) : d213250 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d213268 q = 1) : d213268 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d213298 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21097 q selected
    | true =>
      simp only [d213298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21098 q selected
  have h4 (q : Pattern) (selected : d213299 q = 1) : d216254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213299, d216254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213299, d216254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213305 q = 1) : d213305 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d213306 q = 1) : d216255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213306, d216255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213306, d216255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213307 q = 1) : d216256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213307, d216256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213307, d216256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213308 q = 1) : d216257 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213308, d216257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213308, d216257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d213315 q = 1) : d213315 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d213320 q = 1) : d213320 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d213322 q = 1) : d213322 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d213325 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21100 q selected
    | true =>
      simp only [d213325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21101 q selected
  have h13 (q : Pattern) (selected : d213326 q = 1) : d216259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213326, d216259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213326, d216259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213329 q = 1) : d213329 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d213330 q = 1) : d216260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213330, d216260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d213330, d216260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d213331 q = 1) : d216261 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213331, d216261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213331, d216261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d213332 q = 1) : d216262 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213332, d216262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d213332, d216262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d213333 q = 1) : d216263 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213333, d216263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d213333, d216263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro21103 (p : Pattern) (selected : d213353 p = 1) : d216270 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213322 q = 1) : d213322 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d213325 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21100 q selected
    | true =>
      simp only [d213325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21101 q selected
  have h3 (q : Pattern) (selected : d213326 q = 1) : d216259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213326, d216259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213326, d216259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213329 q = 1) : d213329 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d213330 q = 1) : d216260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213330, d216260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213330, d216260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213351 q = 1) : d216268 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213351, d216268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213351, d216268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213352 q = 1) : d216269 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213352, d216269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213352, d216269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213353 q = 1) : d216270 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213353, d216270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213353, d216270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21104 (p : Pattern) (selected : d213405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1013 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro51 q selected
  have h2 (q : Pattern) (selected : d868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro51 q selected
    | true =>
      simp only [d868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1014 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1015 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d16393 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6823 q selected
  have h7 (q : Pattern) (selected : d9661 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6823 q selected
    | true =>
      simp only [d9661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d16394 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d16394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9663 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d16395 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d16395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213403 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d14689 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6824 q selected
  have h13 (q : Pattern) (selected : d9671 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6824 q selected
    | true =>
      simp only [d9671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d14690 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d14690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d9673 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d14691 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d14691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d1018 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
  have h18 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d1019 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d1019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d875 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d1020 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d1020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d213404 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d213404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d213405 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro21105 (p : Pattern) (selected : d213408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
  have h2 (q : Pattern) (selected : d574 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
    | true =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d575 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1018 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
  have h7 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1019 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d875 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d1020 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213406 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d213407 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d213408 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro21106 (p : Pattern) (selected : d213411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1018 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
  have h2 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1019 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d875 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1020 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213407 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213411 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro21107 (p : Pattern) (selected : d213417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213409 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21104 q selected
    | true =>
      simp only [d213409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21105 q selected
  have h2 (q : Pattern) (selected : d213410 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213412 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21105 q selected
    | true =>
      simp only [d213412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21106 q selected
  have h4 (q : Pattern) (selected : d213413 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213414 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213415 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213416 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213417 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21108 (p : Pattern) (selected : d213421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213412 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21105 q selected
    | true =>
      simp only [d213412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21106 q selected
  have h2 (q : Pattern) (selected : d213413 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213415 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213420 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213421 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21109 (p : Pattern) (selected : d213427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213418 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21107 q selected
    | true =>
      simp only [d213418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213419 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213422 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21108 q selected
    | true =>
      simp only [d213422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213423 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213424 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213425 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213426 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213427 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21110 (p : Pattern) (selected : d213431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213422 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21108 q selected
    | true =>
      simp only [d213422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213423 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213428 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213429 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213430 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213431 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21111 (p : Pattern) (selected : d213443 p = 1) : d216280 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213402 q = 1) : d213402 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d213432 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21109 q selected
    | true =>
      simp only [d213432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21110 q selected
  have h3 (q : Pattern) (selected : d213433 q = 1) : d216276 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213433, d216276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213433, d216276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213439 q = 1) : d213439 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d213440 q = 1) : d216277 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213440, d216277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213440, d216277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213441 q = 1) : d216278 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213441, d216278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213441, d216278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213442 q = 1) : d216279 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213442, d216279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213442, d216279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213443 q = 1) : d216280 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213443, d216280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213443, d216280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21112 (p : Pattern) (selected : d213460 p = 1) : d216286 p = 1 := by
  have h0 (q : Pattern) (selected : d213233 q = 1) : d213233 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213334 q = 1) : d216264 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213334, d216264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21099 q selected
    | true =>
      simp only [d213334, d216264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21102 q selected
  have h2 (q : Pattern) (selected : d213347 q = 1) : d213347 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d213348 q = 1) : d216265 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213348, d216265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213348, d216265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d213349 q = 1) : d216266 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213349, d216266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213349, d216266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213350 q = 1) : d216267 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d213350, d216267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213350, d216267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213354 q = 1) : d216271 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213354, d216271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213354, d216271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21103 q selected
  have h8 (q : Pattern) (selected : d213356 q = 1) : d213356 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d213357 q = 1) : d216272 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213357, d216272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213357, d216272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213358 q = 1) : d216273 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213358, d216273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d213358, d216273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d213359 q = 1) : d216274 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d213359, d216274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213359, d216274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d213360 q = 1) : d216275 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d213360, d216275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213360, d216275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d213444 q = 1) : d216281 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213444, d216281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213444, d216281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21111 q selected
  have h14 (q : Pattern) (selected : d213455 q = 1) : d213455 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d213456 q = 1) : d216282 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213456, d216282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d213456, d216282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d213457 q = 1) : d216283 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213457, d216283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d213457, d216283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d213458 q = 1) : d216284 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d213458, d216284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d213458, d216284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d213459 q = 1) : d216285 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d213459, d216285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d213459, d216285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d213460 q = 1) : d216286 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d213460, d216286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d213460, d216286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro21113 (p : Pattern) (selected : d213466 p = 1) : d216292 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213461 q = 1) : d216287 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d213461, d216287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213461, d216287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21112 q selected
  have h2 (q : Pattern) (selected : d213462 q = 1) : d216288 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d213462, d216288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213462, d216288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213463 q = 1) : d216289 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d213463, d216289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213463, d216289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213464 q = 1) : d216290 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d213464, d216290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213464, d216290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213465 q = 1) : d216291 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d213465, d216291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213465, d216291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213466 q = 1) : d216292 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d213466, d216292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213466, d216292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21114 (p : Pattern) (selected : d213570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1255 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro79 q selected
    | true =>
      simp only [d1255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1256 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1257 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6837 q selected
    | true =>
      simp only [d9896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9898 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16539 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213568 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9908 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6838 q selected
    | true =>
      simp only [d9908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9910 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14868 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
    | true =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d9920 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d14873 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213569 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d213570 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21115 (p : Pattern) (selected : d213573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1265 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro80 q selected
    | true =>
      simp only [d1265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1266 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1267 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1276 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
    | true =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1277 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1278 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213571 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
    | true =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9920 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14873 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213572 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d213573 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro21116 (p : Pattern) (selected : d213578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9943 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6842 q selected
    | true =>
      simp only [d9943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9945 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13057 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213576 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9952 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6843 q selected
    | true =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9954 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14880 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213577 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213578 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21117 (p : Pattern) (selected : d213583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1276 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
    | true =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1277 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1278 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213582 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9952 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6843 q selected
    | true =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9954 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14880 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213577 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213583 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21118 (p : Pattern) (selected : d213588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213574 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21114 q selected
    | true =>
      simp only [d213574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21115 q selected
  have h2 (q : Pattern) (selected : d213575 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213579 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21115 q selected
    | true =>
      simp only [d213579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21116 q selected
  have h4 (q : Pattern) (selected : d213580 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213581 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213584 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21115 q selected
    | true =>
      simp only [d213584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21117 q selected
  have h7 (q : Pattern) (selected : d213585 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213586 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213587 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213588 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d213588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21119 (p : Pattern) (selected : d213592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213584 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21115 q selected
    | true =>
      simp only [d213584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21117 q selected
  have h2 (q : Pattern) (selected : d213585 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213586 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213591 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213592 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21120 (p : Pattern) (selected : d213598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213589 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21118 q selected
    | true =>
      simp only [d213589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213590 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21119 q selected
    | true =>
      simp only [d213593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213595 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213596 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213597 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213598 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21121 (p : Pattern) (selected : d213602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21119 q selected
    | true =>
      simp only [d213593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213601 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213602 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21122 (p : Pattern) (selected : d213622 p = 1) : d216299 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213530 q = 1) : d213530 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d213539 q = 1) : d213539 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d213567 q = 1) : d213567 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d213603 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21120 q selected
    | true =>
      simp only [d213603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21121 q selected
  have h5 (q : Pattern) (selected : d213604 q = 1) : d216295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213604, d216295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213604, d216295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213618 q = 1) : d213618 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d213619 q = 1) : d216296 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213619, d216296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213619, d216296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213620 q = 1) : d216297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213620, d216297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213620, d216297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d213621 q = 1) : d216298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213621, d216298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213621, d216298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213622 q = 1) : d216299 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213622, d216299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213622, d216299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro21123 (p : Pattern) (selected : d213637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213589 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21118 q selected
    | true =>
      simp only [d213589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213590 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21119 q selected
    | true =>
      simp only [d213593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213595 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213596 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213597 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213637 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21124 (p : Pattern) (selected : d213638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21119 q selected
    | true =>
      simp only [d213593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213601 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213638 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21125 (p : Pattern) (selected : d213647 p = 1) : d216304 p = 1 := by
  have h0 (q : Pattern) (selected : d213530 q = 1) : d213530 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213539 q = 1) : d213539 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d213567 q = 1) : d213567 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d213603 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21120 q selected
    | true =>
      simp only [d213603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21121 q selected
  have h4 (q : Pattern) (selected : d213604 q = 1) : d216295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213604, d216295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213604, d216295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213618 q = 1) : d213618 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d213619 q = 1) : d216296 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213619, d216296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213619, d216296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213620 q = 1) : d216297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213620, d216297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213620, d216297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213621 q = 1) : d216298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213621, d216298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213621, d216298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d213628 q = 1) : d213628 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d213633 q = 1) : d213633 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d213636 q = 1) : d213636 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d213639 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21123 q selected
    | true =>
      simp only [d213639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21124 q selected
  have h13 (q : Pattern) (selected : d213640 q = 1) : d216300 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213640, d216300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213640, d216300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213643 q = 1) : d213643 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d213644 q = 1) : d216301 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213644, d216301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d213644, d216301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d213645 q = 1) : d216302 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213645, d216302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213645, d216302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d213646 q = 1) : d216303 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213646, d216303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d213646, d216303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d213647 q = 1) : d216304 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213647, d216304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d213647, d216304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro21126 (p : Pattern) (selected : d213672 p = 1) : d216311 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213636 q = 1) : d213636 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d213639 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21123 q selected
    | true =>
      simp only [d213639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21124 q selected
  have h3 (q : Pattern) (selected : d213640 q = 1) : d216300 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213640, d216300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213640, d216300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213643 q = 1) : d213643 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d213644 q = 1) : d216301 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213644, d216301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213644, d216301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213670 q = 1) : d216309 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213670, d216309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213670, d216309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213671 q = 1) : d216310 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213671, d216310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213671, d216310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213672 q = 1) : d216311 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213672, d216311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213672, d216311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21127 (p : Pattern) (selected : d213733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1438 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro79 q selected
  have h2 (q : Pattern) (selected : d1255 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro79 q selected
    | true =>
      simp only [d1255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1439 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1256 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1440 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d16706 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6837 q selected
  have h7 (q : Pattern) (selected : d9896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6837 q selected
    | true =>
      simp only [d9896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d16707 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d16707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9898 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d16708 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d16708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213731 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15057 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6838 q selected
  have h13 (q : Pattern) (selected : d9908 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6838 q selected
    | true =>
      simp only [d9908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15058 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d9910 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d15059 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d15059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d15064 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
  have h18 (q : Pattern) (selected : d9918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
    | true =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d15065 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d9920 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d15066 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d15066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d213732 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d213732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d213733 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro21128 (p : Pattern) (selected : d213736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro80 q selected
  have h2 (q : Pattern) (selected : d1265 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro80 q selected
    | true =>
      simp only [d1265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1266 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1444 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1447 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
  have h7 (q : Pattern) (selected : d1276 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
    | true =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1448 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d1277 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d1449 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213734 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15064 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
  have h13 (q : Pattern) (selected : d9918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
    | true =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15065 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d9920 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d15066 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d15066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d213735 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d213735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d213736 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro21129 (p : Pattern) (selected : d213741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d13209 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6842 q selected
  have h2 (q : Pattern) (selected : d9943 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6842 q selected
    | true =>
      simp only [d9943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13210 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9945 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13211 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213739 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15073 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6843 q selected
  have h8 (q : Pattern) (selected : d9952 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6843 q selected
    | true =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15074 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9954 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15075 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d213740 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d213741 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro21130 (p : Pattern) (selected : d213746 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1447 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
  have h2 (q : Pattern) (selected : d1276 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
    | true =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1448 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1277 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1449 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213745 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15073 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6843 q selected
  have h8 (q : Pattern) (selected : d9952 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6843 q selected
    | true =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15074 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9954 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15075 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d213740 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d213746 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro21131 (p : Pattern) (selected : d213751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213737 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21127 q selected
    | true =>
      simp only [d213737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21128 q selected
  have h2 (q : Pattern) (selected : d213738 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213742 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21128 q selected
    | true =>
      simp only [d213742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21129 q selected
  have h4 (q : Pattern) (selected : d213743 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213744 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213747 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21128 q selected
    | true =>
      simp only [d213747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21130 q selected
  have h7 (q : Pattern) (selected : d213748 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213749 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213750 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213751 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d213751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21132 (p : Pattern) (selected : d213755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213747 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21128 q selected
    | true =>
      simp only [d213747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21130 q selected
  have h2 (q : Pattern) (selected : d213748 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213749 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213754 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21133 (p : Pattern) (selected : d213761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213752 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21131 q selected
    | true =>
      simp only [d213752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21132 q selected
    | true =>
      simp only [d213756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213758 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213759 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213760 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213761 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21134 (p : Pattern) (selected : d213765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21132 q selected
    | true =>
      simp only [d213756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213762 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213763 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213764 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213765 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21135 (p : Pattern) (selected : d213785 p = 1) : d216321 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213730 q = 1) : d213730 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d213766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21133 q selected
    | true =>
      simp only [d213766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21134 q selected
  have h3 (q : Pattern) (selected : d213767 q = 1) : d216317 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213767, d216317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213767, d216317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213781 q = 1) : d213781 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d213782 q = 1) : d216318 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213782, d216318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213782, d216318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213783 q = 1) : d216319 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213783, d216319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213783, d216319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213784 q = 1) : d216320 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213784, d216320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213784, d216320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213785 q = 1) : d216321 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213785, d216321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213785, d216321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21136 (p : Pattern) (selected : d213802 p = 1) : d216327 p = 1 := by
  have h0 (q : Pattern) (selected : d213522 q = 1) : d213522 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213648 q = 1) : d216305 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213648, d216305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21122 q selected
    | true =>
      simp only [d213648, d216305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21125 q selected
  have h2 (q : Pattern) (selected : d213666 q = 1) : d213666 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d213667 q = 1) : d216306 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213667, d216306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213667, d216306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d213668 q = 1) : d216307 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213668, d216307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213668, d216307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213669 q = 1) : d216308 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d213669, d216308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213669, d216308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213673 q = 1) : d216312 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213673, d216312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213673, d216312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21126 q selected
  have h8 (q : Pattern) (selected : d213675 q = 1) : d213675 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d213676 q = 1) : d216313 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213676, d216313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213676, d216313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213677 q = 1) : d216314 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213677, d216314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d213677, d216314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d213678 q = 1) : d216315 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d213678, d216315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213678, d216315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d213679 q = 1) : d216316 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d213679, d216316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213679, d216316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d213786 q = 1) : d216322 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213786, d216322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213786, d216322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21135 q selected
  have h14 (q : Pattern) (selected : d213797 q = 1) : d213797 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d213798 q = 1) : d216323 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213798, d216323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d213798, d216323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d213799 q = 1) : d216324 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213799, d216324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d213799, d216324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d213800 q = 1) : d216325 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d213800, d216325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d213800, d216325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d213801 q = 1) : d216326 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d213801, d216326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d213801, d216326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d213802 q = 1) : d216327 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d213802, d216327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d213802, d216327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro21137 (p : Pattern) (selected : d213808 p = 1) : d216333 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213803 q = 1) : d216328 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d213803, d216328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213803, d216328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21136 q selected
  have h2 (q : Pattern) (selected : d213804 q = 1) : d216329 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d213804, d216329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213804, d216329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213805 q = 1) : d216330 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d213805, d216330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213805, d216330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213806 q = 1) : d216331 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d213806, d216331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213806, d216331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213807 q = 1) : d216332 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d213807, d216332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213807, d216332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213808 q = 1) : d216333 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d213808, d216333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213808, d216333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21138 (p : Pattern) (selected : d213913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1726 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro113 q selected
    | true =>
      simp only [d1726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1727 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1728 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10190 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6855 q selected
    | true =>
      simp only [d10190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10192 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16891 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213911 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10200 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6856 q selected
    | true =>
      simp only [d10200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10202 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15261 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10215 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
    | true =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d10217 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d15266 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213912 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d213913 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21139 (p : Pattern) (selected : d213916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1741 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro116 q selected
    | true =>
      simp only [d1741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1742 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1743 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10226 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6859 q selected
    | true =>
      simp only [d10226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10228 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16896 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213914 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10215 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
    | true =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10217 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15266 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213915 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d213916 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro21140 (p : Pattern) (selected : d213921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10243 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6861 q selected
    | true =>
      simp only [d10243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10245 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13383 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213919 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10255 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6862 q selected
    | true =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10257 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15273 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213920 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213921 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21141 (p : Pattern) (selected : d213926 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1753 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro117 q selected
    | true =>
      simp only [d1753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1754 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1755 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213925 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10255 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6862 q selected
    | true =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10257 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15273 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213920 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213926 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21142 (p : Pattern) (selected : d213931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213917 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21138 q selected
    | true =>
      simp only [d213917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21139 q selected
  have h2 (q : Pattern) (selected : d213918 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213922 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21139 q selected
    | true =>
      simp only [d213922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21140 q selected
  have h4 (q : Pattern) (selected : d213923 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213924 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213927 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21139 q selected
    | true =>
      simp only [d213927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21141 q selected
  have h7 (q : Pattern) (selected : d213928 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213929 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213930 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213931 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d213931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21143 (p : Pattern) (selected : d213935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213927 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21139 q selected
    | true =>
      simp only [d213927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21141 q selected
  have h2 (q : Pattern) (selected : d213928 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213929 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213934 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213935 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21144 (p : Pattern) (selected : d213941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213932 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21142 q selected
    | true =>
      simp only [d213932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213933 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213936 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21143 q selected
    | true =>
      simp only [d213936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213937 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213938 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213939 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213940 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21145 (p : Pattern) (selected : d213945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213936 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21143 q selected
    | true =>
      simp only [d213936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213937 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213942 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213943 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213944 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213945 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21146 (p : Pattern) (selected : d213965 p = 1) : d216341 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213873 q = 1) : d213873 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d213882 q = 1) : d213882 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d213910 q = 1) : d213910 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d213946 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21144 q selected
    | true =>
      simp only [d213946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21145 q selected
  have h5 (q : Pattern) (selected : d213947 q = 1) : d216337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213947, d216337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213947, d216337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213961 q = 1) : d213961 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d213962 q = 1) : d216338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213962, d216338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213962, d216338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213963 q = 1) : d216339 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213963, d216339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213963, d216339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d213964 q = 1) : d216340 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213964, d216340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213964, d216340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213965 q = 1) : d216341 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213965, d216341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213965, d216341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro21147 (p : Pattern) (selected : d213980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213932 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21142 q selected
    | true =>
      simp only [d213932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213933 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213936 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21143 q selected
    | true =>
      simp only [d213936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213937 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213938 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213939 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213940 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213980 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21148 (p : Pattern) (selected : d213981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213936 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21143 q selected
    | true =>
      simp only [d213936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213937 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213942 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213943 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213944 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213981 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21149 (p : Pattern) (selected : d213990 p = 1) : d216346 p = 1 := by
  have h0 (q : Pattern) (selected : d213873 q = 1) : d213873 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213882 q = 1) : d213882 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d213910 q = 1) : d213910 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d213946 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21144 q selected
    | true =>
      simp only [d213946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21145 q selected
  have h4 (q : Pattern) (selected : d213947 q = 1) : d216337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213947, d216337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213947, d216337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213961 q = 1) : d213961 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d213962 q = 1) : d216338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213962, d216338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213962, d216338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213963 q = 1) : d216339 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213963, d216339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213963, d216339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213964 q = 1) : d216340 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213964, d216340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213964, d216340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d213971 q = 1) : d213971 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d213976 q = 1) : d213976 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d213979 q = 1) : d213979 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d213982 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21147 q selected
    | true =>
      simp only [d213982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21148 q selected
  have h13 (q : Pattern) (selected : d213983 q = 1) : d216342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213983, d216342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213983, d216342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213986 q = 1) : d213986 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d213987 q = 1) : d216343 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213987, d216343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d213987, d216343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d213988 q = 1) : d216344 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213988, d216344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213988, d216344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d213989 q = 1) : d216345 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213989, d216345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d213989, d216345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d213990 q = 1) : d216346 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213990, d216346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d213990, d216346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro21150 (p : Pattern) (selected : d214015 p = 1) : d216353 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213979 q = 1) : d213979 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d213982 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21147 q selected
    | true =>
      simp only [d213982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21148 q selected
  have h3 (q : Pattern) (selected : d213983 q = 1) : d216342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213983, d216342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213983, d216342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213986 q = 1) : d213986 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d213987 q = 1) : d216343 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213987, d216343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213987, d216343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214013 q = 1) : d216351 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214013, d216351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214013, d216351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214014 q = 1) : d216352 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214014, d216352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214014, d216352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214015 q = 1) : d216353 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214015, d216353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214015, d216353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21151 (p : Pattern) (selected : d214076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1915 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro113 q selected
  have h2 (q : Pattern) (selected : d1726 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro113 q selected
    | true =>
      simp only [d1726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1916 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1727 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1917 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17066 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6855 q selected
  have h7 (q : Pattern) (selected : d10190 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6855 q selected
    | true =>
      simp only [d10190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17067 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10192 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17068 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214074 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15450 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6856 q selected
  have h13 (q : Pattern) (selected : d10200 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6856 q selected
    | true =>
      simp only [d10200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15451 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10202 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d15452 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d15452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d15457 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
  have h18 (q : Pattern) (selected : d10215 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
    | true =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d15458 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10217 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d15459 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d15459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d214075 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d214075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d214076 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro21152 (p : Pattern) (selected : d214079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1919 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro116 q selected
  have h2 (q : Pattern) (selected : d1741 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro116 q selected
    | true =>
      simp only [d1741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1920 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1742 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1921 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17073 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6859 q selected
  have h7 (q : Pattern) (selected : d10226 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6859 q selected
    | true =>
      simp only [d10226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17074 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10228 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17075 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214077 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15457 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
  have h13 (q : Pattern) (selected : d10215 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
    | true =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15458 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10217 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d15459 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d15459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d214078 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d214078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d214079 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro21153 (p : Pattern) (selected : d214084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d13535 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6861 q selected
  have h2 (q : Pattern) (selected : d10243 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6861 q selected
    | true =>
      simp only [d10243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13536 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10245 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13537 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214082 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15466 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6862 q selected
  have h8 (q : Pattern) (selected : d10255 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6862 q selected
    | true =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15467 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10257 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15468 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d214083 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d214084 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro21154 (p : Pattern) (selected : d214089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1924 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro117 q selected
  have h2 (q : Pattern) (selected : d1753 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro117 q selected
    | true =>
      simp only [d1753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1925 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1754 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1926 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214088 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15466 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6862 q selected
  have h8 (q : Pattern) (selected : d10255 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6862 q selected
    | true =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15467 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10257 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15468 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d214083 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d214089 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro21155 (p : Pattern) (selected : d214094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214080 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21151 q selected
    | true =>
      simp only [d214080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21152 q selected
  have h2 (q : Pattern) (selected : d214081 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214085 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21152 q selected
    | true =>
      simp only [d214085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21153 q selected
  have h4 (q : Pattern) (selected : d214086 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214087 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214090 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21152 q selected
    | true =>
      simp only [d214090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21154 q selected
  have h7 (q : Pattern) (selected : d214091 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214092 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214093 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214094 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d214094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21156 (p : Pattern) (selected : d214098 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214090 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21152 q selected
    | true =>
      simp only [d214090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21154 q selected
  have h2 (q : Pattern) (selected : d214091 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214092 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214097 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214098 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21157 (p : Pattern) (selected : d214104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214095 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21155 q selected
    | true =>
      simp only [d214095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214096 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214099 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21156 q selected
    | true =>
      simp only [d214099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214100 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214101 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214102 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214103 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214104 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21158 (p : Pattern) (selected : d214108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214099 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21156 q selected
    | true =>
      simp only [d214099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214100 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214105 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214106 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214107 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214108 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21159 (p : Pattern) (selected : d214128 p = 1) : d216363 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214073 q = 1) : d214073 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d214109 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21157 q selected
    | true =>
      simp only [d214109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21158 q selected
  have h3 (q : Pattern) (selected : d214110 q = 1) : d216359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214110, d216359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214110, d216359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d214124 q = 1) : d214124 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d214125 q = 1) : d216360 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214125, d216360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214125, d216360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214126 q = 1) : d216361 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214126, d216361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214126, d216361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214127 q = 1) : d216362 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214127, d216362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214127, d216362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214128 q = 1) : d216363 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214128, d216363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214128, d216363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21160 (p : Pattern) (selected : d214145 p = 1) : d216369 p = 1 := by
  have h0 (q : Pattern) (selected : d213865 q = 1) : d213865 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d213991 q = 1) : d216347 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213991, d216347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21146 q selected
    | true =>
      simp only [d213991, d216347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21149 q selected
  have h2 (q : Pattern) (selected : d214009 q = 1) : d214009 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d214010 q = 1) : d216348 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d214010, d216348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214010, d216348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d214011 q = 1) : d216349 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d214011, d216349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214011, d216349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214012 q = 1) : d216350 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d214012, d216350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214012, d216350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214016 q = 1) : d216354 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214016, d216354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214016, d216354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21150 q selected
  have h8 (q : Pattern) (selected : d214018 q = 1) : d214018 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d214019 q = 1) : d216355 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d214019, d216355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214019, d216355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214020 q = 1) : d216356 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d214020, d216356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d214020, d216356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d214021 q = 1) : d216357 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d214021, d216357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d214021, d216357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d214022 q = 1) : d216358 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d214022, d216358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214022, d216358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d214129 q = 1) : d216364 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214129, d216364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214129, d216364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21159 q selected
  have h14 (q : Pattern) (selected : d214140 q = 1) : d214140 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d214141 q = 1) : d216365 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d214141, d216365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d214141, d216365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d214142 q = 1) : d216366 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d214142, d216366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d214142, d216366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d214143 q = 1) : d216367 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d214143, d216367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d214143, d216367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d214144 q = 1) : d216368 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d214144, d216368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d214144, d216368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d214145 q = 1) : d216369 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d214145, d216369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d214145, d216369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro21161 (p : Pattern) (selected : d214151 p = 1) : d216375 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214146 q = 1) : d216370 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d214146, d216370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214146, d216370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21160 q selected
  have h2 (q : Pattern) (selected : d214147 q = 1) : d216371 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d214147, d216371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214147, d216371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214148 q = 1) : d216372 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d214148, d216372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214148, d216372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d214149 q = 1) : d216373 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d214149, d216373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214149, d216373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214150 q = 1) : d216374 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d214150, d216374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214150, d216374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214151 q = 1) : d216375 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d214151, d216375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214151, d216375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21162 (p : Pattern) (selected : d214256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2201 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro148 q selected
    | true =>
      simp only [d2201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2202 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2203 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10458 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6872 q selected
    | true =>
      simp only [d10458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10460 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17256 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214254 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10468 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6873 q selected
    | true =>
      simp only [d10468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10470 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15649 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
    | true =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d10484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d15654 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d214255 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d214255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d214256 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21163 (p : Pattern) (selected : d214259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2219 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro153 q selected
    | true =>
      simp only [d2219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2220 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2221 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10493 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6876 q selected
    | true =>
      simp only [d10493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10495 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17261 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214257 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
    | true =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15654 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214258 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d214258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d214259 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro21164 (p : Pattern) (selected : d214264 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10508 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6878 q selected
    | true =>
      simp only [d10508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10510 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d214262 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10521 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6879 q selected
    | true =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10523 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15661 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214263 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214264 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21165 (p : Pattern) (selected : d214269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2231 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro154 q selected
    | true =>
      simp only [d2231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2232 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2233 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d214268 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10521 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6879 q selected
    | true =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10523 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15661 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214263 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214269 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21166 (p : Pattern) (selected : d214274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214260 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21162 q selected
    | true =>
      simp only [d214260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21163 q selected
  have h2 (q : Pattern) (selected : d214261 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214265 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21163 q selected
    | true =>
      simp only [d214265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21164 q selected
  have h4 (q : Pattern) (selected : d214266 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214267 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214270 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21163 q selected
    | true =>
      simp only [d214270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21165 q selected
  have h7 (q : Pattern) (selected : d214271 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214272 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214273 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214274 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d214274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21167 (p : Pattern) (selected : d214278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214270 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21163 q selected
    | true =>
      simp only [d214270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21165 q selected
  have h2 (q : Pattern) (selected : d214271 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214272 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214277 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214278 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21168 (p : Pattern) (selected : d214284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214275 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21166 q selected
    | true =>
      simp only [d214275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214276 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214279 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21167 q selected
    | true =>
      simp only [d214279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214280 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214281 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214282 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214283 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214284 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21169 (p : Pattern) (selected : d214288 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214279 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21167 q selected
    | true =>
      simp only [d214279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214280 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214285 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214286 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214287 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214288 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21170 (p : Pattern) (selected : d214308 p = 1) : d216384 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214217 q = 1) : d214217 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d214226 q = 1) : d214226 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d214253 q = 1) : d214253 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d214289 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21168 q selected
    | true =>
      simp only [d214289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21169 q selected
  have h5 (q : Pattern) (selected : d214290 q = 1) : d216380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214290, d216380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214290, d216380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214304 q = 1) : d214304 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d214305 q = 1) : d216381 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214305, d216381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214305, d216381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214306 q = 1) : d216382 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214306, d216382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214306, d216382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d214307 q = 1) : d216383 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214307, d216383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214307, d216383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214308 q = 1) : d216384 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214308, d216384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214308, d216384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro21171 (p : Pattern) (selected : d214323 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214275 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21166 q selected
    | true =>
      simp only [d214275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214276 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214279 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21167 q selected
    | true =>
      simp only [d214279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214280 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214281 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214282 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214283 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214323 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21172 (p : Pattern) (selected : d214324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214279 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21167 q selected
    | true =>
      simp only [d214279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214280 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214285 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214286 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214287 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214324 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21173 (p : Pattern) (selected : d214333 p = 1) : d216389 p = 1 := by
  have h0 (q : Pattern) (selected : d214217 q = 1) : d214217 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214226 q = 1) : d214226 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d214253 q = 1) : d214253 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d214289 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21168 q selected
    | true =>
      simp only [d214289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21169 q selected
  have h4 (q : Pattern) (selected : d214290 q = 1) : d216380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214290, d216380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214290, d216380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214304 q = 1) : d214304 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d214305 q = 1) : d216381 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214305, d216381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214305, d216381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214306 q = 1) : d216382 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214306, d216382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214306, d216382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214307 q = 1) : d216383 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214307, d216383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214307, d216383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d214314 q = 1) : d214314 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d214319 q = 1) : d214319 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d214322 q = 1) : d214322 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d214325 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21171 q selected
    | true =>
      simp only [d214325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21172 q selected
  have h13 (q : Pattern) (selected : d214326 q = 1) : d216385 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214326, d216385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214326, d216385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d214329 q = 1) : d214329 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d214330 q = 1) : d216386 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214330, d216386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d214330, d216386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d214331 q = 1) : d216387 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214331, d216387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d214331, d216387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d214332 q = 1) : d216388 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214332, d216388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d214332, d216388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d214333 q = 1) : d216389 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214333, d216389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d214333, d216389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro21174 (p : Pattern) (selected : d214358 p = 1) : d216396 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214322 q = 1) : d214322 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d214325 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21171 q selected
    | true =>
      simp only [d214325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21172 q selected
  have h3 (q : Pattern) (selected : d214326 q = 1) : d216385 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214326, d216385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214326, d216385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d214329 q = 1) : d214329 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d214330 q = 1) : d216386 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214330, d216386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214330, d216386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214356 q = 1) : d216394 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214356, d216394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214356, d216394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214357 q = 1) : d216395 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214357, d216395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214357, d216395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214358 q = 1) : d216396 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214358, d216396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214358, d216396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21175 (p : Pattern) (selected : d214418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2393 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro148 q selected
  have h2 (q : Pattern) (selected : d2201 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro148 q selected
    | true =>
      simp only [d2201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2394 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2202 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2395 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17430 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6872 q selected
  have h7 (q : Pattern) (selected : d10458 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6872 q selected
    | true =>
      simp only [d10458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17431 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10460 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17432 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214416 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15828 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6873 q selected
  have h13 (q : Pattern) (selected : d10468 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6873 q selected
    | true =>
      simp only [d10468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15829 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10470 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d15830 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d15830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d15835 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
  have h18 (q : Pattern) (selected : d10482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
    | true =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d15836 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d15837 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d15837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d214417 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d214417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d214418 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro21176 (p : Pattern) (selected : d214421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2397 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro153 q selected
  have h2 (q : Pattern) (selected : d2219 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro153 q selected
    | true =>
      simp only [d2219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2398 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2220 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2399 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17437 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6876 q selected
  have h7 (q : Pattern) (selected : d10493 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6876 q selected
    | true =>
      simp only [d10493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17438 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10495 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17439 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214419 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15835 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
  have h13 (q : Pattern) (selected : d10482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
    | true =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15836 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d15837 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d15837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d214420 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d214420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d214421 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro21177 (p : Pattern) (selected : d214426 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d13862 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6878 q selected
  have h2 (q : Pattern) (selected : d10508 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6878 q selected
    | true =>
      simp only [d10508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13863 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10510 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214424 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15844 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6879 q selected
  have h8 (q : Pattern) (selected : d10521 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6879 q selected
    | true =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15845 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10523 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15846 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d214425 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d214426 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro21178 (p : Pattern) (selected : d214431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro154 q selected
  have h2 (q : Pattern) (selected : d2231 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro154 q selected
    | true =>
      simp only [d2231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2232 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214430 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15844 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6879 q selected
  have h8 (q : Pattern) (selected : d10521 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6879 q selected
    | true =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15845 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10523 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15846 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d214425 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d214431 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro21179 (p : Pattern) (selected : d214436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214422 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21175 q selected
    | true =>
      simp only [d214422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21176 q selected
  have h2 (q : Pattern) (selected : d214423 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214427 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21176 q selected
    | true =>
      simp only [d214427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21177 q selected
  have h4 (q : Pattern) (selected : d214428 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214429 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214432 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21176 q selected
    | true =>
      simp only [d214432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21178 q selected
  have h7 (q : Pattern) (selected : d214433 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214434 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214435 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214436 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d214436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21180 (p : Pattern) (selected : d214440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214432 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21176 q selected
    | true =>
      simp only [d214432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21178 q selected
  have h2 (q : Pattern) (selected : d214433 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214434 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214439 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214440 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21181 (p : Pattern) (selected : d214446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214437 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21179 q selected
    | true =>
      simp only [d214437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214438 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214441 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21180 q selected
    | true =>
      simp only [d214441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214442 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214443 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214444 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214445 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214446 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21182 (p : Pattern) (selected : d214450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214441 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21180 q selected
    | true =>
      simp only [d214441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214442 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214447 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214448 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214449 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214450 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21183 (p : Pattern) (selected : d214470 p = 1) : d216406 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214415 q = 1) : d214415 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d214451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21181 q selected
    | true =>
      simp only [d214451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21182 q selected
  have h3 (q : Pattern) (selected : d214452 q = 1) : d216402 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214452, d216402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214452, d216402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d214466 q = 1) : d214466 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d214467 q = 1) : d216403 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214467, d216403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214467, d216403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214468 q = 1) : d216404 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214468, d216404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214468, d216404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214469 q = 1) : d216405 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214469, d216405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214469, d216405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214470 q = 1) : d216406 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214470, d216406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214470, d216406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21184 (p : Pattern) (selected : d214487 p = 1) : d216412 p = 1 := by
  have h0 (q : Pattern) (selected : d214209 q = 1) : d214209 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214334 q = 1) : d216390 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214334, d216390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21170 q selected
    | true =>
      simp only [d214334, d216390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21173 q selected
  have h2 (q : Pattern) (selected : d214352 q = 1) : d214352 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d214353 q = 1) : d216391 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d214353, d216391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214353, d216391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d214354 q = 1) : d216392 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d214354, d216392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214354, d216392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214355 q = 1) : d216393 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d214355, d216393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214355, d216393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214359 q = 1) : d216397 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214359, d216397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214359, d216397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21174 q selected
  have h8 (q : Pattern) (selected : d214361 q = 1) : d214361 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d214362 q = 1) : d216398 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d214362, d216398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214362, d216398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214363 q = 1) : d216399 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d214363, d216399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d214363, d216399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d214364 q = 1) : d216400 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d214364, d216400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d214364, d216400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d214365 q = 1) : d216401 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d214365, d216401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214365, d216401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d214471 q = 1) : d216407 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214471, d216407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214471, d216407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21183 q selected
  have h14 (q : Pattern) (selected : d214482 q = 1) : d214482 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d214483 q = 1) : d216408 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d214483, d216408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d214483, d216408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d214484 q = 1) : d216409 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d214484, d216409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d214484, d216409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d214485 q = 1) : d216410 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d214485, d216410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d214485, d216410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d214486 q = 1) : d216411 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d214486, d216411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d214486, d216411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d214487 q = 1) : d216412 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d214487, d216412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d214487, d216412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro21185 (p : Pattern) (selected : d214493 p = 1) : d216418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214488 q = 1) : d216413 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d214488, d216413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214488, d216413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21184 q selected
  have h2 (q : Pattern) (selected : d214489 q = 1) : d216414 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d214489, d216414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214489, d216414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214490 q = 1) : d216415 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d214490, d216415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214490, d216415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d214491 q = 1) : d216416 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d214491, d216416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214491, d216416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214492 q = 1) : d216417 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d214492, d216417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214492, d216417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214493 q = 1) : d216418 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d214493, d216418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214493, d216418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21186 (p : Pattern) (selected : d214499 p = 1) : d216424 p = 1 := by
  have h0 (q : Pattern) (selected : d213186 q = 1) : d216253 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d213186, d216253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21073 q selected
    | true =>
      simp only [d213186, d216253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21091 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d213467 q = 1) : d216293 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d213467, d216293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213467, d216293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21113 q selected
  have h3 (q : Pattern) (selected : d213468 q = 1) : d216294 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d213468, d216294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213468, d216294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213809 q = 1) : d216334 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d213809, d216334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213809, d216334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21137 q selected
  have h5 (q : Pattern) (selected : d213810 q = 1) : d216335 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d213810, d216335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213810, d216335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213811 q = 1) : d216336 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d213811, d216336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213811, d216336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214152 q = 1) : d216376 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d214152, d216376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214152, d216376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21161 q selected
  have h8 (q : Pattern) (selected : d214153 q = 1) : d216377 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d214153, d216377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214153, d216377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d214154 q = 1) : d216378 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d214154, d216378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214154, d216378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214155 q = 1) : d216379 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d214155, d216379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214155, d216379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214494 q = 1) : d216419 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d214494, d216419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214494, d216419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21185 q selected
  have h12 (q : Pattern) (selected : d214495 q = 1) : d216420 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d214495, d216420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214495, d216420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d214496 q = 1) : d216421 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d214496, d216421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214496, d216421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d214497 q = 1) : d216422 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d214497, d216422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214497, d216422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d214498 q = 1) : d216423 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d214498, d216423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d214498, d216423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d214499 q = 1) : d216424 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d214499, d216424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d214499, d216424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro21187 (p : Pattern) (selected : d214505 p = 1) : d216430 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214500 q = 1) : d216425 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d214500, d216425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21186 q selected
    | true =>
      simp only [d214500, d216425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214501 q = 1) : d216426 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d214501, d216426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214501, d216426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d214502 q = 1) : d216427 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d214502, d216427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214502, d216427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214503 q = 1) : d216428 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d214503, d216428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214503, d216428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214504 q = 1) : d216429 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d214504, d216429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214504, d216429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214505 q = 1) : d216430 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d214505, d216430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214505, d216430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21188 (p : Pattern) (selected : d214511 p = 1) : d216436 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214506 q = 1) : d216431 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d214506, d216431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21187 q selected
    | true =>
      simp only [d214506, d216431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214507 q = 1) : d216432 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d214507, d216432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214507, d216432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d214508 q = 1) : d216433 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d214508, d216433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214508, d216433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214509 q = 1) : d216434 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d214509, d216434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214509, d216434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214510 q = 1) : d216435 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d214510, d216435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214510, d216435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214511 q = 1) : d216436 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d214511, d216436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214511, d216436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21189 (p : Pattern) (selected : d214517 p = 1) : d216442 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214512 q = 1) : d216437 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d214512, d216437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21188 q selected
    | true =>
      simp only [d214512, d216437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214513 q = 1) : d216438 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d214513, d216438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214513, d216438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d214514 q = 1) : d216439 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d214514, d216439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214514, d216439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214515 q = 1) : d216440 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d214515, d216440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214515, d216440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214516 q = 1) : d216441 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d214516, d216441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214516, d216441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214517 q = 1) : d216442 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d214517, d216442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214517, d216442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21190 (p : Pattern) (selected : d214523 p = 1) : d216448 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214518 q = 1) : d216443 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d214518, d216443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21189 q selected
    | true =>
      simp only [d214518, d216443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214519 q = 1) : d216444 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d214519, d216444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214519, d216444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d214520 q = 1) : d216445 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d214520, d216445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214520, d216445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214521 q = 1) : d216446 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d214521, d216446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214521, d216446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214522 q = 1) : d216447 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d214522, d216447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214522, d216447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214523 q = 1) : d216448 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d214523, d216448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214523, d216448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21191 (p : Pattern) (selected : d214529 p = 1) : d216454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214524 q = 1) : d216449 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d214524, d216449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21190 q selected
    | true =>
      simp only [d214524, d216449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214525 q = 1) : d216450 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d214525, d216450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214525, d216450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d214526 q = 1) : d216451 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d214526, d216451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214526, d216451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214527 q = 1) : d216452 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d214527, d216452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214527, d216452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214528 q = 1) : d216453 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d214528, d216453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214528, d216453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214529 q = 1) : d216454 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d214529, d216454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214529, d216454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21192 (p : Pattern) (selected : d214535 p = 1) : d216460 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214530 q = 1) : d216455 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d214530, d216455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21191 q selected
    | true =>
      simp only [d214530, d216455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214531 q = 1) : d216456 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d214531, d216456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214531, d216456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d214532 q = 1) : d216457 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d214532, d216457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214532, d216457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214533 q = 1) : d216458 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d214533, d216458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214533, d216458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214534 q = 1) : d216459 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d214534, d216459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214534, d216459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214535 q = 1) : d216460 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d214535, d216460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214535, d216460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21193 (p : Pattern) (selected : d214541 p = 1) : d216466 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d214536 q = 1) : d216461 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d214536, d216461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21192 q selected
    | true =>
      simp only [d214536, d216461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214537 q = 1) : d216462 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d214537, d216462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214537, d216462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d214538 q = 1) : d216463 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d214538, d216463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214538, d216463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214539 q = 1) : d216464 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d214539, d216464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214539, d216464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214540 q = 1) : d216465 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d214540, d216465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214540, d216465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214541 q = 1) : d216466 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d214541, d216466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214541, d216466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21194 (p : Pattern) (selected : d216731 p = 0) : d219220 p = 1 := by
  have h0 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d13 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14 q = 0) : d51866 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d15 q = 0) : d51867 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d216730 q = 0) : d219219 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d216730, d219219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216730, d219219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d216731 q = 0) : d219220 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d216731, d219220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216731, d219220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro21195 (p : Pattern) (selected : d216736 p = 0) : d219225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216732 q = 0) : d219221 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d216732, d219221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21194 q selected
    | true =>
      simp only [d216732, d219221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216733 q = 0) : d219222 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d216733, d219222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d216733, d219222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d216734 q = 0) : d219223 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d216734, d219223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216734, d219223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216735 q = 0) : d219224 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d216735, d219224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216735, d219224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216736 q = 0) : d219225 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d216736, d219225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216736, d219225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21196 (p : Pattern) (selected : d216742 p = 0) : d219231 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216737 q = 0) : d219226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d216737, d219226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21195 q selected
    | true =>
      simp only [d216737, d219226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216738 q = 0) : d219227 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d216738, d219227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d216738, d219227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d216739 q = 0) : d219228 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d216739, d219228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216739, d219228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d216740 q = 0) : d219229 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d216740, d219229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216740, d219229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216741 q = 0) : d219230 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d216741, d219230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216741, d219230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d216742 q = 0) : d219231 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d216742, d219231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216742, d219231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21197 (p : Pattern) (selected : d216748 p = 0) : d219237 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216743 q = 0) : d219232 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d216743, d219232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21196 q selected
    | true =>
      simp only [d216743, d219232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216744 q = 0) : d219233 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d216744, d219233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216744, d219233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216745 q = 0) : d219234 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d216745, d219234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216745, d219234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d216746 q = 0) : d219235 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d216746, d219235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216746, d219235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216747 q = 0) : d219236 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d216747, d219236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216747, d219236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d216748 q = 0) : d219237 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d216748, d219237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216748, d219237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21198 (p : Pattern) (selected : d216754 p = 0) : d219243 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216749 q = 0) : d219238 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21197 q selected
    | true =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216750 q = 0) : d219239 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216751 q = 0) : d219240 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d216751, d219240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216751, d219240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216752 q = 0) : d219241 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d216752, d219241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216752, d219241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216753 q = 0) : d219242 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d216753, d219242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216753, d219242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d216754 q = 0) : d219243 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d216754, d219243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216754, d219243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21199 (p : Pattern) (selected : d216760 p = 0) : d219249 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216755 q = 0) : d219244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216755, d219244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21198 q selected
    | true =>
      simp only [d216755, d219244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216756 q = 0) : d219245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216756, d219245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d216756, d219245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d216757 q = 0) : d219246 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216757, d219246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216757, d219246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216758 q = 0) : d219247 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216758, d219247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216758, d219247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216759 q = 0) : d219248 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d216759, d219248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216759, d219248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216760 q = 0) : d219249 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d216760, d219249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216760, d219249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21200 (p : Pattern) (selected : d216761 p = 0) : d219250 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216749 q = 0) : d219238 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21197 q selected
    | true =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216750 q = 0) : d219239 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216751 q = 0) : d219240 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d216751, d219240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216751, d219240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216752 q = 0) : d219241 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d216752, d219241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216752, d219241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216753 q = 0) : d219242 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d216753, d219242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216753, d219242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d216761 q = 0) : d219250 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d216761, d219250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216761, d219250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21201 (p : Pattern) (selected : d216767 p = 0) : d219256 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216755 q = 0) : d219244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216755, d219244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21198 q selected
    | true =>
      simp only [d216755, d219244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216756 q = 0) : d219245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216756, d219245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d216756, d219245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d216757 q = 0) : d219246 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216757, d219246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216757, d219246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216758 q = 0) : d219247 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216758, d219247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216758, d219247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216759 q = 0) : d219248 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d216759, d219248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216759, d219248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216762 q = 0) : d219251 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216762, d219251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21200 q selected
    | true =>
      simp only [d216762, d219251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d216763 q = 0) : d219252 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216763, d219252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d216763, d219252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d216764 q = 0) : d219253 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216764, d219253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d216764, d219253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d216765 q = 0) : d219254 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216765, d219254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216765, d219254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d216766 q = 0) : d219255 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d216766, d219255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216766, d219255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d216767 q = 0) : d219256 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d216767, d219256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216767, d219256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21202 (p : Pattern) (selected : d216772 p = 0) : d219261 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216762 q = 0) : d219251 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216762, d219251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21200 q selected
    | true =>
      simp only [d216762, d219251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216763 q = 0) : d219252 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216763, d219252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d216763, d219252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d216764 q = 0) : d219253 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216764, d219253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216764, d219253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216765 q = 0) : d219254 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216765, d219254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216765, d219254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216766 q = 0) : d219255 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d216766, d219255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216766, d219255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216772 q = 0) : d219261 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d216772, d219261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216772, d219261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21203 (p : Pattern) (selected : d216783 p = 0) : d219272 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216778 q = 0) : d219267 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d216778, d219267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216778, d219267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21195 q selected
  have h2 (q : Pattern) (selected : d216737 q = 0) : d219226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d216737, d219226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21195 q selected
    | true =>
      simp only [d216737, d219226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d216779 q = 0) : d219268 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d216779, d219268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d216779, d219268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d216738 q = 0) : d219227 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d216738, d219227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216738, d219227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216780 q = 0) : d219269 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d216780, d219269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216780, d219269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216781 q = 0) : d219270 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d216781, d219270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216781, d219270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d216782 q = 0) : d219271 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d216782, d219271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d216782, d219271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d216783 q = 0) : d219272 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d216783, d219272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d216783, d219272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21204 (p : Pattern) (selected : d216789 p = 0) : d219278 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216784 q = 0) : d219273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d216784, d219273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21203 q selected
    | true =>
      simp only [d216784, d219273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216785 q = 0) : d219274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d216785, d219274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216785, d219274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216786 q = 0) : d219275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d216786, d219275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216786, d219275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d216787 q = 0) : d219276 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d216787, d219276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216787, d219276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216788 q = 0) : d219277 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d216788, d219277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216788, d219277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d216789 q = 0) : d219278 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d216789, d219278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216789, d219278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21205 (p : Pattern) (selected : d216795 p = 0) : d219284 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216790 q = 0) : d219279 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216790, d219279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21204 q selected
    | true =>
      simp only [d216790, d219279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216791 q = 0) : d219280 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216791, d219280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216791, d219280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216792 q = 0) : d219281 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d216792, d219281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216792, d219281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216793 q = 0) : d219282 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d216793, d219282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216793, d219282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216794 q = 0) : d219283 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d216794, d219283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216794, d219283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d216795 q = 0) : d219284 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d216795, d219284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216795, d219284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21206 (p : Pattern) (selected : d216801 p = 0) : d219290 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216796 q = 0) : d219285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216796, d219285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21205 q selected
    | true =>
      simp only [d216796, d219285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216797 q = 0) : d219286 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216797, d219286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d216797, d219286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d216798 q = 0) : d219287 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216798, d219287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216798, d219287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216799 q = 0) : d219288 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216799, d219288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216799, d219288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216800 q = 0) : d219289 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d216800, d219289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216800, d219289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216801 q = 0) : d219290 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d216801, d219290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216801, d219290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21207 (p : Pattern) (selected : d216807 p = 0) : d219296 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216768 q = 0) : d219257 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d216768, d219257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21199 q selected
    | true =>
      simp only [d216768, d219257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21201 q selected
  have h2 (q : Pattern) (selected : d216769 q = 0) : d219258 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d216769, d219258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d216769, d219258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d216770 q = 0) : d219259 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d216770, d219259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216770, d219259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216771 q = 0) : d219260 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d216771, d219260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216771, d219260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216773 q = 0) : d219262 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d216773, d219262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216773, d219262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21202 q selected
  have h6 (q : Pattern) (selected : d216774 q = 0) : d219263 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d216774, d219263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216774, d219263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d216775 q = 0) : d219264 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d216775, d219264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d216775, d219264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d216776 q = 0) : d219265 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d216776, d219265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d216776, d219265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d216777 q = 0) : d219266 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d216777, d219266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216777, d219266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d216802 q = 0) : d219291 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d216802, d219291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216802, d219291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21206 q selected
  have h11 (q : Pattern) (selected : d216803 q = 0) : d219292 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d216803, d219292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d216803, d219292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d216804 q = 0) : d219293 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d216804, d219293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d216804, d219293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d216805 q = 0) : d219294 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d216805, d219294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d216805, d219294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d216806 q = 0) : d219295 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d216806, d219295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d216806, d219295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d216807 q = 0) : d219296 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d216807, d219296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d216807, d219296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21208 (p : Pattern) (selected : d216817 p = 0) : d219306 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216755 q = 0) : d219244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216755, d219244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21198 q selected
    | true =>
      simp only [d216755, d219244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216813 q = 0) : d219302 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216813, d219302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216813, d219302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216814 q = 0) : d219303 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216814, d219303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216814, d219303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216815 q = 0) : d219304 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216815, d219304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216815, d219304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216816 q = 0) : d219305 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d216816, d219305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216816, d219305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216817 q = 0) : d219306 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d216817, d219306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216817, d219306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21209 (p : Pattern) (selected : d216824 p = 0) : d219313 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216755 q = 0) : d219244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216755, d219244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21198 q selected
    | true =>
      simp only [d216755, d219244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216813 q = 0) : d219302 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216813, d219302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216813, d219302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216814 q = 0) : d219303 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216814, d219303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216814, d219303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216815 q = 0) : d219304 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216815, d219304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216815, d219304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216816 q = 0) : d219305 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d216816, d219305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216816, d219305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216762 q = 0) : d219251 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216762, d219251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21200 q selected
    | true =>
      simp only [d216762, d219251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d216820 q = 0) : d219309 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216820, d219309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216820, d219309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d216821 q = 0) : d219310 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216821, d219310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d216821, d219310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d216822 q = 0) : d219311 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216822, d219311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216822, d219311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d216823 q = 0) : d219312 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d216823, d219312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216823, d219312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d216824 q = 0) : d219313 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d216824, d219313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216824, d219313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21210 (p : Pattern) (selected : d216829 p = 0) : d219318 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216749 q = 0) : d219238 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21197 q selected
    | true =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216750 q = 0) : d219239 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216751 q = 0) : d219240 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d216751, d219240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216751, d219240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216752 q = 0) : d219241 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d216752, d219241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216752, d219241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216828 q = 0) : d219317 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d216828, d219317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216828, d219317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216829 q = 0) : d219318 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d216829, d219318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216829, d219318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21211 (p : Pattern) (selected : d216836 p = 0) : d219325 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216749 q = 0) : d219238 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21197 q selected
    | true =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216750 q = 0) : d219239 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216751 q = 0) : d219240 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d216751, d219240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216751, d219240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216834 q = 0) : d219323 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d216834, d219323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216834, d219323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216835 q = 0) : d219324 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d216835, d219324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216835, d219324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d216836 q = 0) : d219325 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d216836, d219325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216836, d219325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21212 (p : Pattern) (selected : d216841 p = 0) : d219330 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d127 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d128 q = 0) : d51979 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14 q = 0) : d51866 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d129 q = 0) : d51980 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d51980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d129, d51980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15 q = 0) : d51867 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d216840 q = 0) : d219329 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d216840, d219329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d216840, d219329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d216730 q = 0) : d219219 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d216730, d219219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d216730, d219219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d216841 q = 0) : d219330 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d216841, d219330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d216841, d219330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro21213 (p : Pattern) (selected : d216846 p = 0) : d219335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216842 q = 0) : d219331 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d216842, d219331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21212 q selected
    | true =>
      simp only [d216842, d219331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216732 q = 0) : d219221 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d216732, d219221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21194 q selected
    | true =>
      simp only [d216732, d219221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d216843 q = 0) : d219332 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d216843, d219332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d216843, d219332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d216733 q = 0) : d219222 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d216733, d219222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216733, d219222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216844 q = 0) : d219333 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d216844, d219333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216844, d219333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216845 q = 0) : d219334 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d216845, d219334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216845, d219334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d216734 q = 0) : d219223 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d216734, d219223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216734, d219223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d216735 q = 0) : d219224 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d216735, d219224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d216735, d219224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d216846 q = 0) : d219335 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d216846, d219335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d216846, d219335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21214 (p : Pattern) (selected : d216852 p = 0) : d219341 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216847 q = 0) : d219336 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d216847, d219336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21213 q selected
    | true =>
      simp only [d216847, d219336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216848 q = 0) : d219337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d216848, d219337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d216848, d219337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d216849 q = 0) : d219338 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d216849, d219338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216849, d219338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d216850 q = 0) : d219339 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d216850, d219339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216850, d219339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216737 q = 0) : d219226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d216737, d219226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21195 q selected
    | true =>
      simp only [d216737, d219226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d216738 q = 0) : d219227 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d216738, d219227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216738, d219227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d216739 q = 0) : d219228 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d216739, d219228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216739, d219228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d216740 q = 0) : d219229 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d216740, d219229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d216740, d219229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d216851 q = 0) : d219340 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d216851, d219340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216851, d219340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d216741 q = 0) : d219230 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d216741, d219230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d216741, d219230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d216852 q = 0) : d219341 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d216852, d219341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d216852, d219341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21215 (p : Pattern) (selected : d216858 p = 0) : d219347 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216853 q = 0) : d219342 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d216853, d219342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21214 q selected
    | true =>
      simp only [d216853, d219342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21196 q selected
  have h2 (q : Pattern) (selected : d216854 q = 0) : d219343 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d216854, d219343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216854, d219343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216855 q = 0) : d219344 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d216855, d219344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216855, d219344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d216743 q = 0) : d219232 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d216743, d219232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21196 q selected
    | true =>
      simp only [d216743, d219232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216744 q = 0) : d219233 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d216744, d219233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216744, d219233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216745 q = 0) : d219234 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d216745, d219234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216745, d219234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d216856 q = 0) : d219345 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d216856, d219345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216856, d219345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d216746 q = 0) : d219235 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d216746, d219235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d216746, d219235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d216857 q = 0) : d219346 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d216857, d219346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d216857, d219346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d216858 q = 0) : d219347 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d216858, d219347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d216858, d219347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21216 (p : Pattern) (selected : d216864 p = 0) : d219353 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216859 q = 0) : d219348 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216859, d219348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21215 q selected
    | true =>
      simp only [d216859, d219348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216860 q = 0) : d219349 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216860, d219349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216860, d219349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216749 q = 0) : d219238 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21197 q selected
    | true =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216750 q = 0) : d219239 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216861 q = 0) : d219350 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d216861, d219350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216861, d219350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216862 q = 0) : d219351 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d216862, d219351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216862, d219351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d216863 q = 0) : d219352 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d216863, d219352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d216863, d219352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d216864 q = 0) : d219353 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d216864, d219353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216864, d219353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21217 (p : Pattern) (selected : d216867 p = 0) : d219220 p = 1 := by
  have h0 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d158 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d159 q = 0) : d51866 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d159, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d160 q = 0) : d51867 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d160, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d160, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d216866 q = 0) : d219219 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d216866, d219219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216866, d219219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d216867 q = 0) : d219220 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d216867, d219220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216867, d219220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro21218 (p : Pattern) (selected : d216872 p = 0) : d219225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216868 q = 0) : d219221 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d216868, d219221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21217 q selected
    | true =>
      simp only [d216868, d219221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216869 q = 0) : d219222 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d216869, d219222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d216869, d219222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d216870 q = 0) : d219223 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d216870, d219223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216870, d219223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216871 q = 0) : d219224 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d216871, d219224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216871, d219224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216872 q = 0) : d219225 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d216872, d219225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216872, d219225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21219 (p : Pattern) (selected : d216878 p = 0) : d219231 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216873 q = 0) : d219226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d216873, d219226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21218 q selected
    | true =>
      simp only [d216873, d219226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216874 q = 0) : d219227 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d216874, d219227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d216874, d219227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d216875 q = 0) : d219228 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d216875, d219228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216875, d219228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d216876 q = 0) : d219229 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d216876, d219229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216876, d219229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216877 q = 0) : d219230 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d216877, d219230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216877, d219230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d216878 q = 0) : d219231 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d216878, d219231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216878, d219231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21220 (p : Pattern) (selected : d216884 p = 0) : d219237 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216879 q = 0) : d219232 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d216879, d219232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21219 q selected
    | true =>
      simp only [d216879, d219232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216880 q = 0) : d219233 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d216880, d219233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216880, d219233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216881 q = 0) : d219234 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d216881, d219234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216881, d219234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d216882 q = 0) : d219235 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d216882, d219235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216882, d219235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216883 q = 0) : d219236 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d216883, d219236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216883, d219236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d216884 q = 0) : d219237 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d216884, d219237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216884, d219237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21221 (p : Pattern) (selected : d216890 p = 0) : d219243 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216885 q = 0) : d219238 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216885, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21220 q selected
    | true =>
      simp only [d216885, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216886 q = 0) : d219239 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216886, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216886, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216887 q = 0) : d219240 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d216887, d219240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216887, d219240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216888 q = 0) : d219241 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d216888, d219241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216888, d219241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216889 q = 0) : d219242 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d216889, d219242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216889, d219242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d216890 q = 0) : d219243 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d216890, d219243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216890, d219243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21222 (p : Pattern) (selected : d216896 p = 0) : d219359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216830 q = 0) : d219319 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216830, d219319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21210 q selected
    | true =>
      simp only [d216830, d219319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216831 q = 0) : d219320 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216831, d219320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216831, d219320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216832 q = 0) : d219321 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216832, d219321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216832, d219321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216833 q = 0) : d219322 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216833, d219322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216833, d219322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216837 q = 0) : d219326 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216837, d219326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21211 q selected
    | true =>
      simp only [d216837, d219326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d216838 q = 0) : d219327 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216838, d219327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216838, d219327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d216839 q = 0) : d219328 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216839, d219328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d216839, d219328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d216865 q = 0) : d219354 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216865, d219354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21216 q selected
    | true =>
      simp only [d216865, d219354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21198 q selected
  have h9 (q : Pattern) (selected : d216891 q = 0) : d219244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216891, d219244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21221 q selected
    | true =>
      simp only [d216891, d219244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d216892 q = 0) : d219355 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216892, d219355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d216892, d219355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d216755 q = 0) : d219244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216755, d219244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21198 q selected
    | true =>
      simp only [d216755, d219244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d216756 q = 0) : d219245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216756, d219245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d216756, d219245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d216893 q = 0) : d219356 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216893, d219356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d216893, d219356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d216894 q = 0) : d219357 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216894, d219357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d216894, d219357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d216895 q = 0) : d219358 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d216895, d219358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216895, d219358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d216896 q = 0) : d219359 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d216896, d219359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216896, d219359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro21223 (p : Pattern) (selected : d216897 p = 0) : d219360 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216749 q = 0) : d219238 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21197 q selected
    | true =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216750 q = 0) : d219239 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216751 q = 0) : d219240 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d216751, d219240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216751, d219240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216752 q = 0) : d219241 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d216752, d219241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216752, d219241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216828 q = 0) : d219317 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d216828, d219317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216828, d219317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216897 q = 0) : d219360 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d216897, d219360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216897, d219360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21224 (p : Pattern) (selected : d216902 p = 0) : d219365 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216749 q = 0) : d219238 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21197 q selected
    | true =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216750 q = 0) : d219239 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216751 q = 0) : d219240 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d216751, d219240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216751, d219240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216834 q = 0) : d219323 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d216834, d219323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216834, d219323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216835 q = 0) : d219324 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d216835, d219324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216835, d219324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d216902 q = 0) : d219365 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d216902, d219365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216902, d219365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21225 (p : Pattern) (selected : d216906 p = 0) : d219369 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216859 q = 0) : d219348 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216859, d219348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21215 q selected
    | true =>
      simp only [d216859, d219348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216860 q = 0) : d219349 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216860, d219349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216860, d219349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216749 q = 0) : d219238 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21197 q selected
    | true =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216750 q = 0) : d219239 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216861 q = 0) : d219350 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d216861, d219350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216861, d219350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216862 q = 0) : d219351 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d216862, d219351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216862, d219351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d216863 q = 0) : d219352 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d216863, d219352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d216863, d219352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d216906 q = 0) : d219369 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d216906, d219369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d216906, d219369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21226 (p : Pattern) (selected : d216908 p = 0) : d219250 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216885 q = 0) : d219238 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216885, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21220 q selected
    | true =>
      simp only [d216885, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216886 q = 0) : d219239 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216886, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216886, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216887 q = 0) : d219240 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d216887, d219240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216887, d219240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216888 q = 0) : d219241 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d216888, d219241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216888, d219241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216889 q = 0) : d219242 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d216889, d219242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216889, d219242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d216908 q = 0) : d219250 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d216908, d219250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216908, d219250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21227 (p : Pattern) (selected : d216914 p = 0) : d219375 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216830 q = 0) : d219319 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216830, d219319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21210 q selected
    | true =>
      simp only [d216830, d219319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216831 q = 0) : d219320 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216831, d219320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216831, d219320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216832 q = 0) : d219321 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216832, d219321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216832, d219321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216833 q = 0) : d219322 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216833, d219322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216833, d219322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216837 q = 0) : d219326 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216837, d219326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21211 q selected
    | true =>
      simp only [d216837, d219326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d216838 q = 0) : d219327 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216838, d219327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216838, d219327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d216839 q = 0) : d219328 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216839, d219328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d216839, d219328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d216865 q = 0) : d219354 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216865, d219354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21216 q selected
    | true =>
      simp only [d216865, d219354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21198 q selected
  have h9 (q : Pattern) (selected : d216891 q = 0) : d219244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216891, d219244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21221 q selected
    | true =>
      simp only [d216891, d219244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d216892 q = 0) : d219355 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216892, d219355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d216892, d219355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d216755 q = 0) : d219244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216755, d219244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21198 q selected
    | true =>
      simp only [d216755, d219244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d216756 q = 0) : d219245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216756, d219245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d216756, d219245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d216893 q = 0) : d219356 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216893, d219356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d216893, d219356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d216894 q = 0) : d219357 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216894, d219357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d216894, d219357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d216895 q = 0) : d219358 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d216895, d219358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216895, d219358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d216898 q = 0) : d219361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216898, d219361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21223 q selected
    | true =>
      simp only [d216898, d219361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d216899 q = 0) : d219362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216899, d219362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216899, d219362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d216900 q = 0) : d219363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216900, d219363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d216900, d219363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d216901 q = 0) : d219364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216901, d219364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216901, d219364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d216903 q = 0) : d219366 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216903, d219366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21224 q selected
    | true =>
      simp only [d216903, d219366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d216904 q = 0) : d219367 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216904, d219367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216904, d219367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d216905 q = 0) : d219368 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216905, d219368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d216905, d219368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d216907 q = 0) : d219370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216907, d219370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21225 q selected
    | true =>
      simp only [d216907, d219370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21200 q selected
  have h24 (q : Pattern) (selected : d216909 q = 0) : d219251 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216909, d219251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21226 q selected
    | true =>
      simp only [d216909, d219251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d216910 q = 0) : d219371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216910, d219371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d216910, d219371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d216762 q = 0) : d219251 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216762, d219251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21200 q selected
    | true =>
      simp only [d216762, d219251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d216763 q = 0) : d219252 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216763, d219252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d216763, d219252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d216911 q = 0) : d219372 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216911, d219372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d216911, d219372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d216912 q = 0) : d219373 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216912, d219373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d216912, d219373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d216913 q = 0) : d219374 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d216913, d219374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d216913, d219374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d216914 q = 0) : d219375 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d216914, d219375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d216914, d219375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro21228 (p : Pattern) (selected : d216916 p = 0) : d219377 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216755 q = 0) : d219244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216755, d219244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21198 q selected
    | true =>
      simp only [d216755, d219244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216813 q = 0) : d219302 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216813, d219302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216813, d219302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216814 q = 0) : d219303 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216814, d219303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216814, d219303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216815 q = 0) : d219304 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216815, d219304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216815, d219304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216816 q = 0) : d219305 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d216816, d219305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216816, d219305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216916 q = 0) : d219377 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d216916, d219377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216916, d219377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21229 (p : Pattern) (selected : d216923 p = 0) : d219384 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216907 q = 0) : d219370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216907, d219370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21225 q selected
    | true =>
      simp only [d216907, d219370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21200 q selected
  have h2 (q : Pattern) (selected : d216909 q = 0) : d219251 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216909, d219251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21226 q selected
    | true =>
      simp only [d216909, d219251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d216910 q = 0) : d219371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216910, d219371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d216910, d219371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d216762 q = 0) : d219251 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216762, d219251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21200 q selected
    | true =>
      simp only [d216762, d219251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216763 q = 0) : d219252 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216763, d219252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216763, d219252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d216911 q = 0) : d219372 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216911, d219372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216911, d219372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d216921 q = 0) : d219382 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216921, d219382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216921, d219382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d216922 q = 0) : d219383 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d216922, d219383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216922, d219383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d216923 q = 0) : d219384 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d216923, d219384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216923, d219384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21230 (p : Pattern) (selected : d216934 p = 0) : d219395 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216929 q = 0) : d219390 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d216929, d219390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216929, d219390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21213 q selected
  have h2 (q : Pattern) (selected : d216847 q = 0) : d219336 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d216847, d219336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21213 q selected
    | true =>
      simp only [d216847, d219336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d216930 q = 0) : d219391 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d216930, d219391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d216930, d219391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d216848 q = 0) : d219337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d216848, d219337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216848, d219337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216931 q = 0) : d219392 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d216931, d219392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216931, d219392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216932 q = 0) : d219393 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d216932, d219393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216932, d219393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d216778 q = 0) : d219267 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d216778, d219267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216778, d219267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21195 q selected
  have h8 (q : Pattern) (selected : d216737 q = 0) : d219226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d216737, d219226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21195 q selected
    | true =>
      simp only [d216737, d219226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d216779 q = 0) : d219268 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d216779, d219268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d216779, d219268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d216738 q = 0) : d219227 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d216738, d219227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d216738, d219227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d216780 q = 0) : d219269 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d216780, d219269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d216780, d219269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d216781 q = 0) : d219270 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d216781, d219270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d216781, d219270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d216933 q = 0) : d219394 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d216933, d219394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d216933, d219394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d216782 q = 0) : d219271 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d216782, d219271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d216782, d219271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d216934 q = 0) : d219395 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d216934, d219395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d216934, d219395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21231 (p : Pattern) (selected : d216940 p = 0) : d219401 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216935 q = 0) : d219396 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d216935, d219396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21230 q selected
    | true =>
      simp only [d216935, d219396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21203 q selected
  have h2 (q : Pattern) (selected : d216936 q = 0) : d219397 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d216936, d219397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216936, d219397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216937 q = 0) : d219398 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d216937, d219398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216937, d219398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d216784 q = 0) : d219273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d216784, d219273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21203 q selected
    | true =>
      simp only [d216784, d219273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216785 q = 0) : d219274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d216785, d219274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216785, d219274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216786 q = 0) : d219275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d216786, d219275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216786, d219275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d216938 q = 0) : d219399 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d216938, d219399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216938, d219399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d216787 q = 0) : d219276 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d216787, d219276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d216787, d219276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d216939 q = 0) : d219400 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d216939, d219400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d216939, d219400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d216940 q = 0) : d219401 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d216940, d219401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d216940, d219401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21232 (p : Pattern) (selected : d216946 p = 0) : d219407 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216941 q = 0) : d219402 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216941, d219402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21231 q selected
    | true =>
      simp only [d216941, d219402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216942 q = 0) : d219403 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216942, d219403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216942, d219403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216790 q = 0) : d219279 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216790, d219279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21204 q selected
    | true =>
      simp only [d216790, d219279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216791 q = 0) : d219280 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216791, d219280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216791, d219280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216943 q = 0) : d219404 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d216943, d219404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216943, d219404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216944 q = 0) : d219405 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d216944, d219405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216944, d219405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d216945 q = 0) : d219406 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d216945, d219406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d216945, d219406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d216946 q = 0) : d219407 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d216946, d219407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d216946, d219407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21233 (p : Pattern) (selected : d216953 p = 0) : d219272 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216948 q = 0) : d219267 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d216948, d219267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216948, d219267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21218 q selected
  have h2 (q : Pattern) (selected : d216873 q = 0) : d219226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d216873, d219226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21218 q selected
    | true =>
      simp only [d216873, d219226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d216949 q = 0) : d219268 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d216949, d219268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d216949, d219268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d216874 q = 0) : d219227 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d216874, d219227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216874, d219227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216950 q = 0) : d219269 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d216950, d219269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216950, d219269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216951 q = 0) : d219270 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d216951, d219270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216951, d219270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d216952 q = 0) : d219271 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d216952, d219271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d216952, d219271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d216953 q = 0) : d219272 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d216953, d219272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d216953, d219272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21234 (p : Pattern) (selected : d216959 p = 0) : d219278 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216954 q = 0) : d219273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d216954, d219273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21233 q selected
    | true =>
      simp only [d216954, d219273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216955 q = 0) : d219274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d216955, d219274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216955, d219274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216956 q = 0) : d219275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d216956, d219275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216956, d219275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d216957 q = 0) : d219276 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d216957, d219276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216957, d219276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216958 q = 0) : d219277 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d216958, d219277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216958, d219277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d216959 q = 0) : d219278 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d216959, d219278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216959, d219278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21235 (p : Pattern) (selected : d216965 p = 0) : d219284 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216960 q = 0) : d219279 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216960, d219279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21234 q selected
    | true =>
      simp only [d216960, d219279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216961 q = 0) : d219280 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216961, d219280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216961, d219280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216962 q = 0) : d219281 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d216962, d219281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216962, d219281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216963 q = 0) : d219282 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d216963, d219282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216963, d219282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216964 q = 0) : d219283 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d216964, d219283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216964, d219283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d216965 q = 0) : d219284 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d216965, d219284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216965, d219284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21236 (p : Pattern) (selected : d216971 p = 0) : d219413 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216947 q = 0) : d219408 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216947, d219408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21232 q selected
    | true =>
      simp only [d216947, d219408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21205 q selected
  have h2 (q : Pattern) (selected : d216966 q = 0) : d219285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216966, d219285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21235 q selected
    | true =>
      simp only [d216966, d219285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d216967 q = 0) : d219409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216967, d219409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d216967, d219409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d216796 q = 0) : d219285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216796, d219285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21205 q selected
    | true =>
      simp only [d216796, d219285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216797 q = 0) : d219286 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216797, d219286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d216797, d219286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d216968 q = 0) : d219410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216968, d219410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216968, d219410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d216969 q = 0) : d219411 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216969, d219411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216969, d219411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d216970 q = 0) : d219412 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d216970, d219412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216970, d219412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d216971 q = 0) : d219413 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d216971, d219413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216971, d219413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21237 (p : Pattern) (selected : d216977 p = 0) : d219419 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216818 q = 0) : d219307 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d216818, d219307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216818, d219307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21208 q selected
  have h2 (q : Pattern) (selected : d216819 q = 0) : d219308 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d216819, d219308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d216819, d219308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d216825 q = 0) : d219314 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d216825, d219314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21208 q selected
    | true =>
      simp only [d216825, d219314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21209 q selected
  have h4 (q : Pattern) (selected : d216826 q = 0) : d219315 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d216826, d219315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216826, d219315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216827 q = 0) : d219316 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d216827, d219316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216827, d219316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216915 q = 0) : d219376 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d216915, d219376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21222 q selected
    | true =>
      simp only [d216915, d219376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21227 q selected
  have h7 (q : Pattern) (selected : d216917 q = 0) : d219378 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d216917, d219378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21228 q selected
    | true =>
      simp only [d216917, d219378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d216918 q = 0) : d219379 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d216918, d219379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d216918, d219379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d216919 q = 0) : d219380 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d216919, d219380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d216919, d219380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d216920 q = 0) : d219381 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d216920, d219381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216920, d219381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d216924 q = 0) : d219385 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d216924, d219385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216924, d219385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21229 q selected
  have h12 (q : Pattern) (selected : d216925 q = 0) : d219386 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d216925, d219386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d216925, d219386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d216926 q = 0) : d219387 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d216926, d219387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d216926, d219387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d216927 q = 0) : d219388 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d216927, d219388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d216927, d219388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d216928 q = 0) : d219389 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d216928, d219389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d216928, d219389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d216972 q = 0) : d219414 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d216972, d219414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216972, d219414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21236 q selected
  have h17 (q : Pattern) (selected : d216973 q = 0) : d219415 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d216973, d219415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d216973, d219415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d216974 q = 0) : d219416 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d216974, d219416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d216974, d219416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d216975 q = 0) : d219417 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d216975, d219417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d216975, d219417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d216976 q = 0) : d219418 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d216976, d219418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d216976, d219418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d216977 q = 0) : d219419 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d216977, d219419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d216977, d219419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro21238 (p : Pattern) (selected : d216983 p = 0) : d219425 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216808 q = 0) : d219297 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d216808, d219297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216808, d219297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21207 q selected
  have h2 (q : Pattern) (selected : d216809 q = 0) : d219298 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d216809, d219298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216809, d219298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216810 q = 0) : d219299 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d216810, d219299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216810, d219299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d216811 q = 0) : d219300 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d216811, d219300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216811, d219300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216812 q = 0) : d219301 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d216812, d219301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216812, d219301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216978 q = 0) : d219420 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d216978, d219420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216978, d219420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21237 q selected
  have h7 (q : Pattern) (selected : d216979 q = 0) : d219421 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d216979, d219421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216979, d219421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d216980 q = 0) : d219422 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d216980, d219422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216980, d219422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d216981 q = 0) : d219423 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d216981, d219423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216981, d219423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d216982 q = 0) : d219424 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d216982, d219424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216982, d219424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d216983 q = 0) : d219425 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d216983, d219425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216983, d219425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21239 (p : Pattern) (selected : d216988 p = 0) : d219430 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216865 q = 0) : d219354 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216865, d219354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21216 q selected
    | true =>
      simp only [d216865, d219354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21198 q selected
  have h2 (q : Pattern) (selected : d216984 q = 0) : d219426 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216984, d219426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216984, d219426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216985 q = 0) : d219427 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216985, d219427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216985, d219427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216986 q = 0) : d219428 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216986, d219428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216986, d219428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216987 q = 0) : d219429 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d216987, d219429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216987, d219429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216988 q = 0) : d219430 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d216988, d219430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216988, d219430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21240 (p : Pattern) (selected : d216995 p = 0) : d219437 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216865 q = 0) : d219354 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216865, d219354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21216 q selected
    | true =>
      simp only [d216865, d219354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21198 q selected
  have h2 (q : Pattern) (selected : d216984 q = 0) : d219426 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216984, d219426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216984, d219426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216985 q = 0) : d219427 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216985, d219427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216985, d219427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216986 q = 0) : d219428 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216986, d219428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216986, d219428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216987 q = 0) : d219429 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d216987, d219429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216987, d219429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216907 q = 0) : d219370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d216907, d219370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21225 q selected
    | true =>
      simp only [d216907, d219370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21200 q selected
  have h7 (q : Pattern) (selected : d216991 q = 0) : d219433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d216991, d219433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216991, d219433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d216992 q = 0) : d219434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d216992, d219434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d216992, d219434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d216993 q = 0) : d219435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d216993, d219435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216993, d219435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d216994 q = 0) : d219436 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d216994, d219436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216994, d219436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d216995 q = 0) : d219437 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d216995, d219437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216995, d219437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21241 (p : Pattern) (selected : d217000 p = 0) : d219442 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216859 q = 0) : d219348 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216859, d219348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21215 q selected
    | true =>
      simp only [d216859, d219348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216860 q = 0) : d219349 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216860, d219349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216860, d219349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216749 q = 0) : d219238 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21197 q selected
    | true =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216750 q = 0) : d219239 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216861 q = 0) : d219350 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d216861, d219350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216861, d219350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216862 q = 0) : d219351 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d216862, d219351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216862, d219351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d216999 q = 0) : d219441 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d216999, d219441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216999, d219441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d217000 q = 0) : d219442 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d217000, d219442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d217000, d219442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21242 (p : Pattern) (selected : d217007 p = 0) : d219449 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216859 q = 0) : d219348 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216859, d219348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21215 q selected
    | true =>
      simp only [d216859, d219348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216860 q = 0) : d219349 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216860, d219349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216860, d219349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d216749 q = 0) : d219238 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21197 q selected
    | true =>
      simp only [d216749, d219238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d216750 q = 0) : d219239 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216750, d219239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d216861 q = 0) : d219350 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d216861, d219350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216861, d219350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d217005 q = 0) : d219447 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d217005, d219447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d217005, d219447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d217006 q = 0) : d219448 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d217006, d219448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d217006, d219448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d217007 q = 0) : d219449 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d217007, d219449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d217007, d219449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21243 (p : Pattern) (selected : d217012 p = 0) : d219454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d127 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d307 q = 0) : d52106 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d308 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d309 q = 0) : d52108 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d52108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d309, d52108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d128 q = 0) : d51979 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14 q = 0) : d51866 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d129 q = 0) : d51980 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d51980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d129, d51980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d217011 q = 0) : d219453 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d217011, d219453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d217011, d219453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15 q = 0) : d51867 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d216840 q = 0) : d219329 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d216840, d219329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d216840, d219329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d217012 q = 0) : d219454 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d217012, d219454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d217012, d219454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro21244 (p : Pattern) (selected : d217016 p = 0) : d219458 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d127 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d128 q = 0) : d51979 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14 q = 0) : d51866 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d129 q = 0) : d51980 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d51980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d129, d51980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d217015 q = 0) : d219457 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d217015, d219457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d217015, d219457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15 q = 0) : d51867 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d216730 q = 0) : d219219 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d216730, d219219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d216730, d219219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d217016 q = 0) : d219458 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d217016, d219458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d217016, d219458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro21245 (p : Pattern) (selected : d217021 p = 0) : d219463 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d217013 q = 0) : d219455 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d217013, d219455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21243 q selected
    | true =>
      simp only [d217013, d219455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216842 q = 0) : d219331 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d216842, d219331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21212 q selected
    | true =>
      simp only [d216842, d219331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d217014 q = 0) : d219456 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d217014, d219456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d217014, d219456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d217017 q = 0) : d219459 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d217017, d219459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21244 q selected
    | true =>
      simp only [d217017, d219459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216732 q = 0) : d219221 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d216732, d219221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21194 q selected
    | true =>
      simp only [d216732, d219221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d217018 q = 0) : d219460 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d217018, d219460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d217018, d219460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d217019 q = 0) : d219461 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d217019, d219461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d217019, d219461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d217020 q = 0) : d219462 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d217020, d219462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d217020, d219462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d216843 q = 0) : d219332 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d216843, d219332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216843, d219332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h10 (q : Pattern) (selected : d216733 q = 0) : d219222 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d216733, d219222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216733, d219222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d216844 q = 0) : d219333 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d216844, d219333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d216844, d219333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d216845 q = 0) : d219334 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d216845, d219334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d216845, d219334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d217021 q = 0) : d219463 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d217021, d219463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d217021, d219463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro21246 (p : Pattern) (selected : d217026 p = 0) : d219468 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216842 q = 0) : d219331 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d216842, d219331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21212 q selected
    | true =>
      simp only [d216842, d219331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d216732 q = 0) : d219221 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d216732, d219221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21194 q selected
    | true =>
      simp only [d216732, d219221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d216843 q = 0) : d219332 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d216843, d219332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d216843, d219332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d216733 q = 0) : d219222 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d216733, d219222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216733, d219222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d216844 q = 0) : d219333 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d216844, d219333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216844, d219333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216845 q = 0) : d219334 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d216845, d219334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d216845, d219334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d217026 q = 0) : d219468 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d217026, d219468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d217026, d219468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro21247 (p : Pattern) (selected : d217035 p = 0) : d219477 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d216842 q = 0) : d219331 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d216842, d219331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21212 q selected
    | true =>
      simp only [d216842, d219331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d217032 q = 0) : d219474 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d217032, d219474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d217032, d219474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d217033 q = 0) : d219475 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d217033, d219475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d217033, d219475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d217034 q = 0) : d219476 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d217034, d219476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d217034, d219476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d217035 q = 0) : d219477 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d217035, d219477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d217035, d219477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21248 (p : Pattern) (selected : d217041 p = 0) : d219483 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d217022 q = 0) : d219464 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d217022, d219464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21245 q selected
    | true =>
      simp only [d217022, d219464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d217023 q = 0) : d219465 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d217023, d219465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d217023, d219465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d217024 q = 0) : d219466 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d217024, d219466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d217024, d219466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d217025 q = 0) : d219467 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d217025, d219467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d217025, d219467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d217027 q = 0) : d219469 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d217027, d219469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21246 q selected
    | true =>
      simp only [d217027, d219469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d217028 q = 0) : d219470 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d217028, d219470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d217028, d219470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d217029 q = 0) : d219471 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d217029, d219471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d217029, d219471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d217030 q = 0) : d219472 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d217030, d219472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d217030, d219472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d217031 q = 0) : d219473 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d217031, d219473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d217031, d219473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d217036 q = 0) : d219478 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d217036, d219478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21247 q selected
    | true =>
      simp only [d217036, d219478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d217037 q = 0) : d219479 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d217037, d219479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d217037, d219479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d217038 q = 0) : d219480 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d217038, d219480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d217038, d219480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d217039 q = 0) : d219481 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d217039, d219481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d217039, d219481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d216737 q = 0) : d219226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d216737, d219226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21195 q selected
    | true =>
      simp only [d216737, d219226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d216738 q = 0) : d219227 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d216738, d219227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d216738, d219227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d216739 q = 0) : d219228 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d216739, d219228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216739, d219228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d216740 q = 0) : d219229 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d216740, d219229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d216740, d219229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d217040 q = 0) : d219482 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d217040, d219482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d217040, d219482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d217041 q = 0) : d219483 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d217041, d219483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d217041, d219483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro21249 (p : Pattern) (selected : d217047 p = 0) : d219489 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d217042 q = 0) : d219484 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d217042, d219484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21248 q selected
    | true =>
      simp only [d217042, d219484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21214 q selected
  have h2 (q : Pattern) (selected : d217043 q = 0) : d219485 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d217043, d219485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d217043, d219485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d217044 q = 0) : d219486 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d217044, d219486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d217044, d219486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d216853 q = 0) : d219342 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d216853, d219342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21214 q selected
    | true =>
      simp only [d216853, d219342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21196 q selected
  have h5 (q : Pattern) (selected : d216854 q = 0) : d219343 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d216854, d219343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216854, d219343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d216855 q = 0) : d219344 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d216855, d219344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216855, d219344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d217045 q = 0) : d219487 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d217045, d219487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d217045, d219487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d216743 q = 0) : d219232 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d216743, d219232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21196 q selected
    | true =>
      simp only [d216743, d219232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d216744 q = 0) : d219233 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d216744, d219233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216744, d219233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d216745 q = 0) : d219234 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d216745, d219234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d216745, d219234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d216856 q = 0) : d219345 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d216856, d219345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d216856, d219345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d217046 q = 0) : d219488 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d217046, d219488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d217046, d219488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d217047 q = 0) : d219489 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d217047, d219489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d217047, d219489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
end NetHack.Soko22Hazard87
