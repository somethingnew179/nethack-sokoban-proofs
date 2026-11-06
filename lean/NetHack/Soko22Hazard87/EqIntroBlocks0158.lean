import NetHack.Soko22Hazard87.EqIntroBlocks0157
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro39500 (p : Pattern) (selected : d377068 p = 0) : d378265 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376952 q = 0) : d378210 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376952, d378210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39478 q selected
    | true =>
      simp only [d376952, d378210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39479 q selected
  have h2 (q : Pattern) (selected : d376953 q = 0) : d378211 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376953, d378211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376953, d378211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376954 q = 0) : d378212 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376954, d378212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376954, d378212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376955 q = 0) : d378213 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376955, d378213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376955, d378213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376962 q = 0) : d378220 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376962, d378220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39480 q selected
    | true =>
      simp only [d376962, d378220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39481 q selected
  have h6 (q : Pattern) (selected : d376963 q = 0) : d378221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376963, d378221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376963, d378221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376964 q = 0) : d378222 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376964, d378222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376964, d378222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376996 q = 0) : d378254 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376996, d378254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39487 q selected
    | true =>
      simp only [d376996, d378254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39472 q selected
  have h9 (q : Pattern) (selected : d377057 q = 0) : d378187 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377057, d378187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39497 q selected
    | true =>
      simp only [d377057, d378187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39498 q selected
  have h10 (q : Pattern) (selected : d377058 q = 0) : d378255 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377058, d378255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377058, d378255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377063 q = 0) : d378260 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377063, d378260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39499 q selected
    | true =>
      simp only [d377063, d378260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d377064 q = 0) : d378261 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377064, d378261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d377064, d378261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d377065 q = 0) : d378262 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377065, d378262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377065, d378262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d377066 q = 0) : d378263 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377066, d378263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377066, d378263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d377067 q = 0) : d378264 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377067, d378264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377067, d378264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d377068 q = 0) : d378265 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377068, d378265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377068, d378265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro39501 (p : Pattern) (selected : d377069 p = 0) : d378266 p = 1 := by
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
  have h8 (q : Pattern) (selected : d377069 q = 0) : d378266 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377069, d378266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377069, d378266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39502 (p : Pattern) (selected : d377070 p = 0) : d378267 p = 1 := by
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
  have h6 (q : Pattern) (selected : d377070 q = 0) : d378267 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377070, d378267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377070, d378267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39503 (p : Pattern) (selected : d377075 p = 0) : d378272 p = 1 := by
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
  have h8 (q : Pattern) (selected : d377075 q = 0) : d378272 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377075, d378272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377075, d378272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39504 (p : Pattern) (selected : d377076 p = 0) : d378273 p = 1 := by
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
  have h6 (q : Pattern) (selected : d377076 q = 0) : d378273 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377076, d378273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377076, d378273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39505 (p : Pattern) (selected : d377080 p = 0) : d378277 p = 1 := by
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
  have h8 (q : Pattern) (selected : d377080 q = 0) : d378277 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377080, d378277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377080, d378277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39506 (p : Pattern) (selected : d377082 p = 0) : d378195 p = 1 := by
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
  have h8 (q : Pattern) (selected : d377082 q = 0) : d378195 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377082, d378195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377082, d378195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39507 (p : Pattern) (selected : d377083 p = 0) : d378196 p = 1 := by
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
  have h6 (q : Pattern) (selected : d377083 q = 0) : d378196 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377083, d378196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377083, d378196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39508 (p : Pattern) (selected : d377086 p = 0) : d378280 p = 1 := by
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
  have h6 (q : Pattern) (selected : d377086 q = 0) : d378280 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377086, d378280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377086, d378280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39509 (p : Pattern) (selected : d377092 p = 0) : d378286 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376952 q = 0) : d378210 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376952, d378210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39478 q selected
    | true =>
      simp only [d376952, d378210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39479 q selected
  have h2 (q : Pattern) (selected : d376953 q = 0) : d378211 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376953, d378211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376953, d378211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376954 q = 0) : d378212 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376954, d378212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376954, d378212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376955 q = 0) : d378213 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376955, d378213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376955, d378213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376962 q = 0) : d378220 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376962, d378220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39480 q selected
    | true =>
      simp only [d376962, d378220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39481 q selected
  have h6 (q : Pattern) (selected : d376963 q = 0) : d378221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376963, d378221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376963, d378221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376964 q = 0) : d378222 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376964, d378222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376964, d378222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376996 q = 0) : d378254 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376996, d378254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39487 q selected
    | true =>
      simp only [d376996, d378254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39472 q selected
  have h9 (q : Pattern) (selected : d377057 q = 0) : d378187 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377057, d378187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39497 q selected
    | true =>
      simp only [d377057, d378187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39498 q selected
  have h10 (q : Pattern) (selected : d377058 q = 0) : d378255 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377058, d378255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377058, d378255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377063 q = 0) : d378260 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377063, d378260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39499 q selected
    | true =>
      simp only [d377063, d378260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d377064 q = 0) : d378261 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377064, d378261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d377064, d378261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d377065 q = 0) : d378262 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377065, d378262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377065, d378262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d377066 q = 0) : d378263 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377066, d378263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377066, d378263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d377067 q = 0) : d378264 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377067, d378264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377067, d378264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d377071 q = 0) : d378268 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377071, d378268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39501 q selected
    | true =>
      simp only [d377071, d378268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39502 q selected
  have h17 (q : Pattern) (selected : d377072 q = 0) : d378269 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377072, d378269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377072, d378269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d377073 q = 0) : d378270 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377073, d378270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d377073, d378270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d377074 q = 0) : d378271 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377074, d378271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377074, d378271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d377077 q = 0) : d378274 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377077, d378274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39503 q selected
    | true =>
      simp only [d377077, d378274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39504 q selected
  have h21 (q : Pattern) (selected : d377078 q = 0) : d378275 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377078, d378275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377078, d378275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d377079 q = 0) : d378276 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377079, d378276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d377079, d378276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d377081 q = 0) : d378278 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377081, d378278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39505 q selected
    | true =>
      simp only [d377081, d378278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39475 q selected
  have h24 (q : Pattern) (selected : d377084 q = 0) : d378197 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377084, d378197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39506 q selected
    | true =>
      simp only [d377084, d378197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39507 q selected
  have h25 (q : Pattern) (selected : d377085 q = 0) : d378279 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377085, d378279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d377085, d378279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d377087 q = 0) : d378281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377087, d378281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39508 q selected
    | true =>
      simp only [d377087, d378281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d377088 q = 0) : d378282 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377088, d378282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d377088, d378282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d377089 q = 0) : d378283 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377089, d378283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d377089, d378283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d377090 q = 0) : d378284 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377090, d378284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d377090, d378284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d377091 q = 0) : d378285 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377091, d378285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d377091, d378285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d377092 q = 0) : d378286 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377092, d378286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d377092, d378286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro39510 (p : Pattern) (selected : d377099 p = 0) : d378293 p = 1 := by
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
  have h6 (q : Pattern) (selected : d377094 q = 0) : d378288 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377094, d378288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39473 q selected
    | true =>
      simp only [d377094, d378288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377095 q = 0) : d378289 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377095, d378289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377095, d378289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377096 q = 0) : d378290 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377096, d378290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377096, d378290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377097 q = 0) : d378291 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377097, d378291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377097, d378291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377098 q = 0) : d378292 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377098, d378292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377098, d378292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377099 q = 0) : d378293 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377099, d378293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377099, d378293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39511 (p : Pattern) (selected : d377105 p = 0) : d378299 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377094 q = 0) : d378288 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377094, d378288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39473 q selected
    | true =>
      simp only [d377094, d378288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377095 q = 0) : d378289 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377095, d378289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377095, d378289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377096 q = 0) : d378290 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377096, d378290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377096, d378290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377097 q = 0) : d378291 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377097, d378291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377097, d378291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377098 q = 0) : d378292 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377098, d378292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377098, d378292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377100 q = 0) : d378294 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377100, d378294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39476 q selected
    | true =>
      simp only [d377100, d378294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377101 q = 0) : d378295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377101, d378295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377101, d378295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377102 q = 0) : d378296 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377102, d378296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377102, d378296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377103 q = 0) : d378297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377103, d378297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377103, d378297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377104 q = 0) : d378298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377104, d378298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377104, d378298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377105 q = 0) : d378299 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377105, d378299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377105, d378299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39512 (p : Pattern) (selected : d377112 p = 0) : d378306 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377081 q = 0) : d378278 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377081, d378278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39505 q selected
    | true =>
      simp only [d377081, d378278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39475 q selected
  have h2 (q : Pattern) (selected : d377084 q = 0) : d378197 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377084, d378197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39506 q selected
    | true =>
      simp only [d377084, d378197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39507 q selected
  have h3 (q : Pattern) (selected : d377085 q = 0) : d378279 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377085, d378279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377085, d378279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377087 q = 0) : d378281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377087, d378281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39508 q selected
    | true =>
      simp only [d377087, d378281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377088 q = 0) : d378282 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377088, d378282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377088, d378282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377089 q = 0) : d378283 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377089, d378283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377089, d378283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377110 q = 0) : d378304 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377110, d378304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377110, d378304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377111 q = 0) : d378305 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377111, d378305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377111, d378305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d377112 q = 0) : d378306 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377112, d378306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377112, d378306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro39513 (p : Pattern) (selected : d377114 p = 0) : d378308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377100 q = 0) : d378294 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377100, d378294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39476 q selected
    | true =>
      simp only [d377100, d378294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377101 q = 0) : d378295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377101, d378295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377101, d378295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377102 q = 0) : d378296 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377102, d378296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377102, d378296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377103 q = 0) : d378297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377103, d378297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377103, d378297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377104 q = 0) : d378298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377104, d378298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377104, d378298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377114 q = 0) : d378308 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377114, d378308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377114, d378308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39514 (p : Pattern) (selected : d377130 p = 0) : d378324 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377120 q = 0) : d378314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377120, d378314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377120, d378314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39482 q selected
  have h2 (q : Pattern) (selected : d376968 q = 0) : d378226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376968, d378226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39482 q selected
    | true =>
      simp only [d376968, d378226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377121 q = 0) : d378315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377121, d378315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377121, d378315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376969 q = 0) : d378227 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376969, d378227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376969, d378227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377122 q = 0) : d378316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377122, d378316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377122, d378316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377123 q = 0) : d378317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377123, d378317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377123, d378317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377124 q = 0) : d378318 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377124, d378318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377124, d378318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39483 q selected
  have h8 (q : Pattern) (selected : d376973 q = 0) : d378231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376973, d378231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39483 q selected
    | true =>
      simp only [d376973, d378231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377125 q = 0) : d378319 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377125, d378319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377125, d378319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376974 q = 0) : d378232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376974, d378232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376974, d378232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d377126 q = 0) : d378320 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377126, d378320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377126, d378320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d377127 q = 0) : d378321 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377127, d378321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d377127, d378321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d377128 q = 0) : d378322 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377128, d378322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377128, d378322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h20 (q : Pattern) (selected : d377129 q = 0) : d378323 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377129, d378323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377129, d378323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d377130 q = 0) : d378324 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377130, d378324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377130, d378324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro39515 (p : Pattern) (selected : d377136 p = 0) : d378330 p = 1 := by
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
  have h20 (q : Pattern) (selected : d377131 q = 0) : d378325 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377131, d378325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377131, d378325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39466 q selected
  have h21 (q : Pattern) (selected : d376895 q = 0) : d378153 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376895, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39466 q selected
    | true =>
      simp only [d376895, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d377132 q = 0) : d378326 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377132, d378326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d377132, d378326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d376896 q = 0) : d378154 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376896, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d376896, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d377133 q = 0) : d378327 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377133, d378327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d377133, d378327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d377134 q = 0) : d378328 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377134, d378328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d377134, d378328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d377135 q = 0) : d378329 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377135, d378329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d377135, d378329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d377136 q = 0) : d378330 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377136, d378330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377136, d378330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro39516 (p : Pattern) (selected : d377141 p = 0) : d378335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376789 q = 0) : d378079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376789, d378079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376789, d378079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39420 q selected
  have h2 (q : Pattern) (selected : d376652 q = 0) : d377988 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376652, d377988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39420 q selected
    | true =>
      simp only [d376652, d377988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376790 q = 0) : d378080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376790, d378080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376790, d378080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376653 q = 0) : d377989 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376653, d377989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376653, d377989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376791 q = 0) : d378081 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376791, d378081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376791, d378081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376792 q = 0) : d378082 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376792, d378082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376792, d378082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377131 q = 0) : d378325 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377131, d378325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377131, d378325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39466 q selected
  have h8 (q : Pattern) (selected : d376895 q = 0) : d378153 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376895, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39466 q selected
    | true =>
      simp only [d376895, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377132 q = 0) : d378326 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377132, d378326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377132, d378326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376896 q = 0) : d378154 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376896, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376896, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d377133 q = 0) : d378327 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377133, d378327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377133, d378327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d377134 q = 0) : d378328 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377134, d378328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d377134, d378328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d377135 q = 0) : d378329 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377135, d378329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377135, d378329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d377140 q = 0) : d378334 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377140, d378334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d377140, d378334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d377141 q = 0) : d378335 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377141, d378335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377141, d378335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro39517 (p : Pattern) (selected : d377147 p = 0) : d378341 p = 1 := by
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
  have h7 (q : Pattern) (selected : d377131 q = 0) : d378325 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377131, d378325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377131, d378325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39466 q selected
  have h8 (q : Pattern) (selected : d376895 q = 0) : d378153 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376895, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39466 q selected
    | true =>
      simp only [d376895, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377132 q = 0) : d378326 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377132, d378326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377132, d378326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376896 q = 0) : d378154 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376896, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376896, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d377133 q = 0) : d378327 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377133, d378327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377133, d378327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d377134 q = 0) : d378328 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377134, d378328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d377134, d378328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d377146 q = 0) : d378340 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377146, d378340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377146, d378340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d377140 q = 0) : d378334 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377140, d378334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d377140, d378334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d377147 q = 0) : d378341 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377147, d378341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377147, d378341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro39518 (p : Pattern) (selected : d377151 p = 0) : d378345 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377131 q = 0) : d378325 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377131, d378325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377131, d378325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39466 q selected
  have h2 (q : Pattern) (selected : d376895 q = 0) : d378153 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376895, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39466 q selected
    | true =>
      simp only [d376895, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377132 q = 0) : d378326 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377132, d378326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377132, d378326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376896 q = 0) : d378154 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376896, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376896, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377133 q = 0) : d378327 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377133, d378327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377133, d378327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377134 q = 0) : d378328 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377134, d378328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377134, d378328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377140 q = 0) : d378334 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377140, d378334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377140, d378334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377151 q = 0) : d378345 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377151, d378345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377151, d378345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39519 (p : Pattern) (selected : d377157 p = 0) : d378351 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377137 q = 0) : d378331 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377137, d378331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39514 q selected
    | true =>
      simp only [d377137, d378331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39515 q selected
  have h2 (q : Pattern) (selected : d377138 q = 0) : d378332 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377138, d378332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377138, d378332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377139 q = 0) : d378333 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377139, d378333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377139, d378333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377142 q = 0) : d378336 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377142, d378336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39515 q selected
    | true =>
      simp only [d377142, d378336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39516 q selected
  have h5 (q : Pattern) (selected : d377143 q = 0) : d378337 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377143, d378337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377143, d378337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377144 q = 0) : d378338 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377144, d378338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377144, d378338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377145 q = 0) : d378339 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377145, d378339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377145, d378339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377148 q = 0) : d378342 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377148, d378342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39515 q selected
    | true =>
      simp only [d377148, d378342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39517 q selected
  have h9 (q : Pattern) (selected : d377149 q = 0) : d378343 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377149, d378343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377149, d378343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377150 q = 0) : d378344 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377150, d378344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377150, d378344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377152 q = 0) : d378346 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377152, d378346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39517 q selected
    | true =>
      simp only [d377152, d378346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39518 q selected
  have h12 (q : Pattern) (selected : d377153 q = 0) : d378347 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377153, d378347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377153, d378347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d377154 q = 0) : d378348 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377154, d378348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377154, d378348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d377155 q = 0) : d378349 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377155, d378349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377155, d378349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d377156 q = 0) : d378350 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377156, d378350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377156, d378350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d377157 q = 0) : d378351 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377157, d378351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d377157, d378351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro39520 (p : Pattern) (selected : d377162 p = 0) : d378356 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377148 q = 0) : d378342 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377148, d378342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39515 q selected
    | true =>
      simp only [d377148, d378342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39517 q selected
  have h2 (q : Pattern) (selected : d377149 q = 0) : d378343 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377149, d378343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377149, d378343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377150 q = 0) : d378344 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377150, d378344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377150, d378344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377152 q = 0) : d378346 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377152, d378346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39517 q selected
    | true =>
      simp only [d377152, d378346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39518 q selected
  have h5 (q : Pattern) (selected : d377153 q = 0) : d378347 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377153, d378347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377153, d378347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377154 q = 0) : d378348 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377154, d378348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377154, d378348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377155 q = 0) : d378349 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377155, d378349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377155, d378349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377160 q = 0) : d378354 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377160, d378354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377160, d378354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377161 q = 0) : d378355 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377161, d378355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377161, d378355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377162 q = 0) : d378356 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377162, d378356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377162, d378356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39521 (p : Pattern) (selected : d377168 p = 0) : d378362 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377158 q = 0) : d378352 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377158, d378352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39519 q selected
    | true =>
      simp only [d377158, d378352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377159 q = 0) : d378353 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377159, d378353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377159, d378353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377163 q = 0) : d378357 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377163, d378357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39520 q selected
    | true =>
      simp only [d377163, d378357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377164 q = 0) : d378358 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377164, d378358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377164, d378358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377165 q = 0) : d378359 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377165, d378359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377165, d378359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377166 q = 0) : d378360 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377166, d378360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377166, d378360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377167 q = 0) : d378361 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377167, d378361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377167, d378361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377168 q = 0) : d378362 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377168, d378362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377168, d378362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39522 (p : Pattern) (selected : d377170 p = 0) : d378364 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377152 q = 0) : d378346 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377152, d378346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39517 q selected
    | true =>
      simp only [d377152, d378346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39518 q selected
  have h2 (q : Pattern) (selected : d377153 q = 0) : d378347 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377153, d378347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377153, d378347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377154 q = 0) : d378348 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377154, d378348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377154, d378348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377160 q = 0) : d378354 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377160, d378354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377160, d378354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377169 q = 0) : d378363 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377169, d378363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377169, d378363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377170 q = 0) : d378364 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377170, d378364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377170, d378364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39523 (p : Pattern) (selected : d377176 p = 0) : d378370 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377163 q = 0) : d378357 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377163, d378357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39520 q selected
    | true =>
      simp only [d377163, d378357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377164 q = 0) : d378358 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377164, d378358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377164, d378358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377171 q = 0) : d378365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377171, d378365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39522 q selected
    | true =>
      simp only [d377171, d378365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377172 q = 0) : d378366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377172, d378366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377172, d378366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377173 q = 0) : d378367 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377173, d378367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377173, d378367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377174 q = 0) : d378368 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377174, d378368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377174, d378368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377175 q = 0) : d378369 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377175, d378369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377175, d378369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377176 q = 0) : d378370 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377176, d378370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377176, d378370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39524 (p : Pattern) (selected : d377196 p = 0) : d378330 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377178 q = 0) : d378070 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377178, d378070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377178, d378070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39488 q selected
  have h2 (q : Pattern) (selected : d377001 q = 0) : d377971 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377001, d377971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39488 q selected
    | true =>
      simp only [d377001, d377971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377179 q = 0) : d378071 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377179, d378071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377179, d378071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377002 q = 0) : d377972 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377002, d377972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377002, d377972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377180 q = 0) : d378072 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377180, d378072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377180, d378072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377181 q = 0) : d378073 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377181, d378073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377181, d378073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377182 q = 0) : d378074 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377182, d378074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377182, d378074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39489 q selected
  have h8 (q : Pattern) (selected : d377009 q = 0) : d377979 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377009, d377979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39489 q selected
    | true =>
      simp only [d377009, d377979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377183 q = 0) : d378075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377183, d378075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377183, d378075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377010 q = 0) : d377980 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377010, d377980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377010, d377980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d377184 q = 0) : d378076 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377184, d378076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377184, d378076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d377185 q = 0) : d378077 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377185, d378077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d377185, d378077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d377186 q = 0) : d378078 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377186, d378078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377186, d378078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d377187 q = 0) : d378079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377187, d378079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377187, d378079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39490 q selected
  have h15 (q : Pattern) (selected : d377018 q = 0) : d377988 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377018, d377988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39490 q selected
    | true =>
      simp only [d377018, d377988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d377188 q = 0) : d378080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377188, d378080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d377188, d378080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d377019 q = 0) : d377989 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377019, d377989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d377019, d377989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d377189 q = 0) : d378081 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377189, d378081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d377189, d378081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d377190 q = 0) : d378082 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377190, d378082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d377190, d378082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d377191 q = 0) : d378325 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377191, d378325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377191, d378325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39491 q selected
  have h21 (q : Pattern) (selected : d377023 q = 0) : d378153 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377023, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39491 q selected
    | true =>
      simp only [d377023, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d377192 q = 0) : d378326 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377192, d378326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d377192, d378326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d377024 q = 0) : d378154 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377024, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d377024, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d377193 q = 0) : d378327 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377193, d378327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d377193, d378327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d377194 q = 0) : d378328 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377194, d378328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d377194, d378328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d377195 q = 0) : d378329 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377195, d378329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d377195, d378329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d377196 q = 0) : d378330 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377196, d378330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377196, d378330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro39525 (p : Pattern) (selected : d377199 p = 0) : d378341 p = 1 := by
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
  have h7 (q : Pattern) (selected : d377191 q = 0) : d378325 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377191, d378325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377191, d378325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39491 q selected
  have h8 (q : Pattern) (selected : d377023 q = 0) : d378153 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377023, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39491 q selected
    | true =>
      simp only [d377023, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377192 q = 0) : d378326 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377192, d378326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377192, d378326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377024 q = 0) : d378154 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377024, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377024, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d377193 q = 0) : d378327 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377193, d378327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377193, d378327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d377194 q = 0) : d378328 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377194, d378328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d377194, d378328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d377197 q = 0) : d378340 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377197, d378340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377197, d378340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d377198 q = 0) : d378334 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377198, d378334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d377198, d378334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d377199 q = 0) : d378341 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377199, d378341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377199, d378341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro39526 (p : Pattern) (selected : d377203 p = 0) : d378345 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377191 q = 0) : d378325 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377191, d378325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377191, d378325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39491 q selected
  have h2 (q : Pattern) (selected : d377023 q = 0) : d378153 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377023, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39491 q selected
    | true =>
      simp only [d377023, d378153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377192 q = 0) : d378326 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377192, d378326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377192, d378326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377024 q = 0) : d378154 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377024, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377024, d378154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377193 q = 0) : d378327 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377193, d378327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377193, d378327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377194 q = 0) : d378328 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377194, d378328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377194, d378328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377198 q = 0) : d378334 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377198, d378334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377198, d378334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377203 q = 0) : d378345 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377203, d378345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377203, d378345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39527 (p : Pattern) (selected : d377210 p = 0) : d378356 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377200 q = 0) : d378342 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377200, d378342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39524 q selected
    | true =>
      simp only [d377200, d378342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39525 q selected
  have h2 (q : Pattern) (selected : d377201 q = 0) : d378343 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377201, d378343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377201, d378343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377202 q = 0) : d378344 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377202, d378344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377202, d378344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377204 q = 0) : d378346 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377204, d378346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39525 q selected
    | true =>
      simp only [d377204, d378346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39526 q selected
  have h5 (q : Pattern) (selected : d377205 q = 0) : d378347 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377205, d378347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377205, d378347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377206 q = 0) : d378348 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377206, d378348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377206, d378348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377207 q = 0) : d378349 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377207, d378349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377207, d378349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377208 q = 0) : d378354 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377208, d378354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377208, d378354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377209 q = 0) : d378355 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377209, d378355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377209, d378355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377210 q = 0) : d378356 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377210, d378356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377210, d378356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39528 (p : Pattern) (selected : d377214 p = 0) : d378364 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377204 q = 0) : d378346 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377204, d378346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39525 q selected
    | true =>
      simp only [d377204, d378346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39526 q selected
  have h2 (q : Pattern) (selected : d377205 q = 0) : d378347 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377205, d378347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377205, d378347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377206 q = 0) : d378348 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377206, d378348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377206, d378348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377208 q = 0) : d378354 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377208, d378354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377208, d378354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377213 q = 0) : d378363 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377213, d378363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377213, d378363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377214 q = 0) : d378364 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377214, d378364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377214, d378364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39529 (p : Pattern) (selected : d377220 p = 0) : d378370 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377211 q = 0) : d378357 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377211, d378357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39527 q selected
    | true =>
      simp only [d377211, d378357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377212 q = 0) : d378358 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377212, d378358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377212, d378358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377215 q = 0) : d378365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377215, d378365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39528 q selected
    | true =>
      simp only [d377215, d378365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377216 q = 0) : d378366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377216, d378366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377216, d378366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377217 q = 0) : d378367 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377217, d378367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377217, d378367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377218 q = 0) : d378368 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377218, d378368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377218, d378368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377219 q = 0) : d378369 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377219, d378369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377219, d378369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377220 q = 0) : d378370 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377220, d378370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377220, d378370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39530 (p : Pattern) (selected : d377224 p = 0) : d378375 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377215 q = 0) : d378365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377215, d378365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39528 q selected
    | true =>
      simp only [d377215, d378365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377216 q = 0) : d378366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377216, d378366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377216, d378366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377221 q = 0) : d378372 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377221, d378372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377221, d378372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377222 q = 0) : d378373 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377222, d378373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377222, d378373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377223 q = 0) : d378374 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377223, d378374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377223, d378374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377224 q = 0) : d378375 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377224, d378375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377224, d378375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39531 (p : Pattern) (selected : d377230 p = 0) : d378381 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377163 q = 0) : d378357 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377163, d378357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39520 q selected
    | true =>
      simp only [d377163, d378357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377164 q = 0) : d378358 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377164, d378358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377164, d378358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377227 q = 0) : d378378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377227, d378378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377227, d378378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377228 q = 0) : d378379 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377228, d378379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377228, d378379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377229 q = 0) : d378380 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377229, d378380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377229, d378380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377230 q = 0) : d378381 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377230, d378381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377230, d378381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39532 (p : Pattern) (selected : d377236 p = 0) : d378387 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377177 q = 0) : d378371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377177, d378371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39521 q selected
    | true =>
      simp only [d377177, d378371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39523 q selected
  have h2 (q : Pattern) (selected : d377225 q = 0) : d378376 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377225, d378376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39529 q selected
    | true =>
      simp only [d377225, d378376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39530 q selected
  have h3 (q : Pattern) (selected : d377226 q = 0) : d378377 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377226, d378377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377226, d378377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377231 q = 0) : d378382 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377231, d378382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39531 q selected
    | true =>
      simp only [d377231, d378382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377232 q = 0) : d378383 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377232, d378383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377232, d378383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377233 q = 0) : d378384 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377233, d378384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377233, d378384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377234 q = 0) : d378385 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377234, d378385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377234, d378385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377235 q = 0) : d378386 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377235, d378386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377235, d378386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d377236 q = 0) : d378387 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377236, d378387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377236, d378387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro39533 (p : Pattern) (selected : d377241 p = 0) : d378375 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377171 q = 0) : d378365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377171, d378365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39522 q selected
    | true =>
      simp only [d377171, d378365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377172 q = 0) : d378366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377172, d378366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377172, d378366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377238 q = 0) : d378372 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377238, d378372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377238, d378372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377239 q = 0) : d378373 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377239, d378373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377239, d378373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377240 q = 0) : d378374 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377240, d378374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377240, d378374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377241 q = 0) : d378375 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377241, d378375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377241, d378375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39534 (p : Pattern) (selected : d377247 p = 0) : d378394 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377242 q = 0) : d378389 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377242, d378389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39533 q selected
    | true =>
      simp only [d377242, d378389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377243 q = 0) : d378390 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377243, d378390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377243, d378390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377244 q = 0) : d378391 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377244, d378391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377244, d378391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377245 q = 0) : d378392 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377245, d378392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377245, d378392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377246 q = 0) : d378393 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377246, d378393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377246, d378393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377247 q = 0) : d378394 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377247, d378394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377247, d378394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39535 (p : Pattern) (selected : d377253 p = 0) : d378400 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d376935 q = 0) : d378193 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376935, d378193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376935, d378193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39474 q selected
  have h2 (q : Pattern) (selected : d376936 q = 0) : d378194 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376936, d378194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376936, d378194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376945 q = 0) : d378203 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376945, d378203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39474 q selected
    | true =>
      simp only [d376945, d378203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39477 q selected
  have h4 (q : Pattern) (selected : d376946 q = 0) : d378204 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376946, d378204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376946, d378204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376947 q = 0) : d378205 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376947, d378205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376947, d378205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377093 q = 0) : d378287 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377093, d378287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39500 q selected
    | true =>
      simp only [d377093, d378287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39509 q selected
  have h7 (q : Pattern) (selected : d377106 q = 0) : d378300 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377106, d378300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39510 q selected
    | true =>
      simp only [d377106, d378300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39511 q selected
  have h8 (q : Pattern) (selected : d377107 q = 0) : d378301 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d377107, d378301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377107, d378301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d377108 q = 0) : d378302 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d377108, d378302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377108, d378302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d377109 q = 0) : d378303 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d377109, d378303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377109, d378303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377113 q = 0) : d378307 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377113, d378307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377113, d378307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39512 q selected
  have h12 (q : Pattern) (selected : d377115 q = 0) : d378309 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377115, d378309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377115, d378309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39513 q selected
  have h13 (q : Pattern) (selected : d377116 q = 0) : d378310 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d377116, d378310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d377116, d378310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d377117 q = 0) : d378311 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d377117, d378311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377117, d378311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d377118 q = 0) : d378312 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d377118, d378312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d377118, d378312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d377119 q = 0) : d378313 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d377119, d378313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377119, d378313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d377237 q = 0) : d378388 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377237, d378388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377237, d378388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39532 q selected
  have h18 (q : Pattern) (selected : d377248 q = 0) : d378395 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377248, d378395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377248, d378395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39534 q selected
  have h19 (q : Pattern) (selected : d377249 q = 0) : d378396 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d377249, d378396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d377249, d378396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d377250 q = 0) : d378397 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d377250, d378397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d377250, d378397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d377251 q = 0) : d378398 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d377251, d378398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d377251, d378398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d377252 q = 0) : d378399 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d377252, d378399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d377252, d378399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d377253 q = 0) : d378400 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d377253, d378400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d377253, d378400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro39536 (p : Pattern) (selected : d377259 p = 0) : d378406 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377254 q = 0) : d378401 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d377254, d378401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377254, d378401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39535 q selected
  have h2 (q : Pattern) (selected : d377255 q = 0) : d378402 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d377255, d378402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377255, d378402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377256 q = 0) : d378403 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d377256, d378403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377256, d378403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377257 q = 0) : d378404 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d377257, d378404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377257, d378404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377258 q = 0) : d378405 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d377258, d378405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377258, d378405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377259 q = 0) : d378406 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d377259, d378406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377259, d378406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39537 (p : Pattern) (selected : d377270 p = 0) : d378417 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d353146 q = 0) : d355080 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d353146, d355080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d353146, d355080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36591 q selected
  have h2 (q : Pattern) (selected : d377264 q = 0) : d378411 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d377264, d378411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377264, d378411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377265 q = 0) : d378412 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377265, d378412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377265, d378412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351904 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36591 q selected
    | true =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377266 q = 0) : d378413 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d377266, d378413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377266, d378413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377267 q = 0) : d378414 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377267, d378414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377267, d378414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377268 q = 0) : d378415 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d377268, d378415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377268, d378415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377269 q = 0) : d378416 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d377269, d378416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377269, d378416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377270 q = 0) : d378417 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d377270, d378417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377270, d378417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro39538 (p : Pattern) (selected : d377276 p = 0) : d378423 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377271 q = 0) : d378418 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377271, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39537 q selected
    | true =>
      simp only [d377271, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377272 q = 0) : d378419 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377272, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377272, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377273 q = 0) : d378420 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377273, d378420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377273, d378420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377274 q = 0) : d378421 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377274, d378421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377274, d378421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377275 q = 0) : d378422 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377275, d378422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377275, d378422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377276 q = 0) : d378423 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377276, d378423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377276, d378423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39539 (p : Pattern) (selected : d377278 p = 0) : d378425 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377271 q = 0) : d378418 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377271, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39537 q selected
    | true =>
      simp only [d377271, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377272 q = 0) : d378419 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377272, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377272, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377273 q = 0) : d378420 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377273, d378420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377273, d378420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377274 q = 0) : d378421 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377274, d378421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377274, d378421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377275 q = 0) : d378422 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377275, d378422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377275, d378422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377277 q = 0) : d378424 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377277, d378424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377277, d378424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377278 q = 0) : d378425 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377278, d378425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377278, d378425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro39540 (p : Pattern) (selected : d377282 p = 0) : d378429 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d353146 q = 0) : d355080 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d353146, d355080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d353146, d355080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36591 q selected
  have h2 (q : Pattern) (selected : d377264 q = 0) : d378411 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d377264, d378411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377264, d378411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377265 q = 0) : d378412 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377265, d378412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377265, d378412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351904 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36591 q selected
    | true =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377266 q = 0) : d378413 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d377266, d378413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377266, d378413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377267 q = 0) : d378414 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377267, d378414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377267, d378414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377268 q = 0) : d378415 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d377268, d378415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377268, d378415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377269 q = 0) : d378416 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d377269, d378416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377269, d378416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377282 q = 0) : d378429 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d377282, d378429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377282, d378429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro39541 (p : Pattern) (selected : d377288 p = 0) : d378435 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377271 q = 0) : d378418 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377271, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39537 q selected
    | true =>
      simp only [d377271, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377272 q = 0) : d378419 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377272, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377272, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377273 q = 0) : d378420 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377273, d378420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377273, d378420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377274 q = 0) : d378421 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377274, d378421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377274, d378421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377277 q = 0) : d378424 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377277, d378424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377277, d378424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377283 q = 0) : d378430 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377283, d378430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39540 q selected
    | true =>
      simp only [d377283, d378430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377284 q = 0) : d378431 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377284, d378431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377284, d378431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377285 q = 0) : d378432 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377285, d378432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377285, d378432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d377286 q = 0) : d378433 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377286, d378433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377286, d378433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d377287 q = 0) : d378434 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377287, d378434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377287, d378434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d377288 q = 0) : d378435 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377288, d378435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377288, d378435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39542 (p : Pattern) (selected : d377295 p = 0) : d378442 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377279 q = 0) : d378426 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377279, d378426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39538 q selected
    | true =>
      simp only [d377279, d378426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39539 q selected
  have h2 (q : Pattern) (selected : d377280 q = 0) : d378427 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377280, d378427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377280, d378427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377281 q = 0) : d378428 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377281, d378428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377281, d378428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377289 q = 0) : d378436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377289, d378436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39539 q selected
    | true =>
      simp only [d377289, d378436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39541 q selected
  have h5 (q : Pattern) (selected : d377290 q = 0) : d378437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377290, d378437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377290, d378437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377291 q = 0) : d378438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377291, d378438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377291, d378438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377292 q = 0) : d378439 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377292, d378439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377292, d378439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377293 q = 0) : d378440 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377293, d378440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377293, d378440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377294 q = 0) : d378441 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377294, d378441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377294, d378441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377295 q = 0) : d378442 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377295, d378442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377295, d378442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39543 (p : Pattern) (selected : d377299 p = 0) : d378446 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377289 q = 0) : d378436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377289, d378436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39539 q selected
    | true =>
      simp only [d377289, d378436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39541 q selected
  have h2 (q : Pattern) (selected : d377290 q = 0) : d378437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377290, d378437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377290, d378437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377291 q = 0) : d378438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377291, d378438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377291, d378438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377293 q = 0) : d378440 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377293, d378440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377293, d378440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377298 q = 0) : d378445 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377298, d378445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377298, d378445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377299 q = 0) : d378446 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377299, d378446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377299, d378446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39544 (p : Pattern) (selected : d377305 p = 0) : d378452 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377296 q = 0) : d378443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377296, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39542 q selected
    | true =>
      simp only [d377296, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377297 q = 0) : d378444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377297, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377297, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377300 q = 0) : d378447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39543 q selected
    | true =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377301 q = 0) : d378448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377302 q = 0) : d378449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377302, d378449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377302, d378449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377303 q = 0) : d378450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377303, d378450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377303, d378450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377304 q = 0) : d378451 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377304, d378451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377304, d378451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377305 q = 0) : d378452 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377305, d378452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377305, d378452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39545 (p : Pattern) (selected : d377309 p = 0) : d378456 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377300 q = 0) : d378447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39543 q selected
    | true =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377301 q = 0) : d378448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377306 q = 0) : d378453 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377306, d378453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377306, d378453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377307 q = 0) : d378454 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377307, d378454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377307, d378454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377308 q = 0) : d378455 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377308, d378455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377308, d378455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377309 q = 0) : d378456 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377309, d378456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377309, d378456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39546 (p : Pattern) (selected : d377315 p = 0) : d378462 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377310 q = 0) : d378457 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377310, d378457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39544 q selected
    | true =>
      simp only [d377310, d378457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39545 q selected
  have h2 (q : Pattern) (selected : d377311 q = 0) : d378458 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377311, d378458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377311, d378458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377312 q = 0) : d378459 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377312, d378459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377312, d378459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377313 q = 0) : d378460 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377313, d378460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377313, d378460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377314 q = 0) : d378461 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377314, d378461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377314, d378461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377315 q = 0) : d378462 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377315, d378462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377315, d378462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39547 (p : Pattern) (selected : d377318 p = 0) : d378465 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377296 q = 0) : d378443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377296, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39542 q selected
    | true =>
      simp only [d377296, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377297 q = 0) : d378444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377297, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377297, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377300 q = 0) : d378447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39543 q selected
    | true =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377301 q = 0) : d378448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377302 q = 0) : d378449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377302, d378449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377302, d378449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377303 q = 0) : d378450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377303, d378450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377303, d378450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377304 q = 0) : d378451 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377304, d378451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377304, d378451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377318 q = 0) : d378465 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377318, d378465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377318, d378465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39548 (p : Pattern) (selected : d377319 p = 0) : d378466 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377300 q = 0) : d378447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39543 q selected
    | true =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377301 q = 0) : d378448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377306 q = 0) : d378453 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377306, d378453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377306, d378453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377307 q = 0) : d378454 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377307, d378454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377307, d378454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377308 q = 0) : d378455 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377308, d378455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377308, d378455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377319 q = 0) : d378466 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377319, d378466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377319, d378466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39549 (p : Pattern) (selected : d377325 p = 0) : d378472 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377310 q = 0) : d378457 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377310, d378457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39544 q selected
    | true =>
      simp only [d377310, d378457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39545 q selected
  have h2 (q : Pattern) (selected : d377311 q = 0) : d378458 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377311, d378458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377311, d378458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377312 q = 0) : d378459 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377312, d378459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377312, d378459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377313 q = 0) : d378460 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377313, d378460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377313, d378460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377314 q = 0) : d378461 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377314, d378461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377314, d378461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377320 q = 0) : d378467 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377320, d378467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39547 q selected
    | true =>
      simp only [d377320, d378467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39548 q selected
  have h7 (q : Pattern) (selected : d377321 q = 0) : d378468 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377321, d378468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377321, d378468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377322 q = 0) : d378469 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377322, d378469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377322, d378469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377323 q = 0) : d378470 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377323, d378470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377323, d378470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377324 q = 0) : d378471 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377324, d378471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377324, d378471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377325 q = 0) : d378472 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377325, d378472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377325, d378472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39550 (p : Pattern) (selected : d377330 p = 0) : d378477 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377296 q = 0) : d378443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377296, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39542 q selected
    | true =>
      simp only [d377296, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377297 q = 0) : d378444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377297, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377297, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377300 q = 0) : d378447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39543 q selected
    | true =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377301 q = 0) : d378448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377302 q = 0) : d378449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377302, d378449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377302, d378449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377303 q = 0) : d378450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377303, d378450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377303, d378450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377329 q = 0) : d378476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377329, d378476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377329, d378476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377330 q = 0) : d378477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377330, d378477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377330, d378477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39551 (p : Pattern) (selected : d377332 p = 0) : d378479 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377300 q = 0) : d378447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39543 q selected
    | true =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377301 q = 0) : d378448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377306 q = 0) : d378453 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377306, d378453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377306, d378453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377307 q = 0) : d378454 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377307, d378454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377307, d378454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377331 q = 0) : d378478 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377331, d378478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377331, d378478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377332 q = 0) : d378479 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377332, d378479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377332, d378479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39552 (p : Pattern) (selected : d377339 p = 0) : d378486 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377296 q = 0) : d378443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377296, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39542 q selected
    | true =>
      simp only [d377296, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377297 q = 0) : d378444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377297, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377297, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377300 q = 0) : d378447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39543 q selected
    | true =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377301 q = 0) : d378448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377302 q = 0) : d378449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377302, d378449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377302, d378449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377337 q = 0) : d378484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377337, d378484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377337, d378484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377338 q = 0) : d378485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377338, d378485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377338, d378485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377339 q = 0) : d378486 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377339, d378486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377339, d378486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39553 (p : Pattern) (selected : d377342 p = 0) : d378489 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377300 q = 0) : d378447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39543 q selected
    | true =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377301 q = 0) : d378448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377306 q = 0) : d378453 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377306, d378453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377306, d378453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377340 q = 0) : d378487 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377340, d378487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377340, d378487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377341 q = 0) : d378488 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377341, d378488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377341, d378488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377342 q = 0) : d378489 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377342, d378489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377342, d378489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39554 (p : Pattern) (selected : d377351 p = 0) : d378498 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377346 q = 0) : d378493 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377346, d378493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377346, d378493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39538 q selected
  have h2 (q : Pattern) (selected : d377347 q = 0) : d378494 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377347, d378494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377347, d378494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377348 q = 0) : d378495 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377348, d378495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377348, d378495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377279 q = 0) : d378426 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377279, d378426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39538 q selected
    | true =>
      simp only [d377279, d378426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39539 q selected
  have h5 (q : Pattern) (selected : d377280 q = 0) : d378427 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377280, d378427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377280, d378427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377281 q = 0) : d378428 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377281, d378428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377281, d378428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377349 q = 0) : d378496 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377349, d378496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377349, d378496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377289 q = 0) : d378436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377289, d378436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39539 q selected
    | true =>
      simp only [d377289, d378436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39541 q selected
  have h9 (q : Pattern) (selected : d377290 q = 0) : d378437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377290, d378437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377290, d378437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377291 q = 0) : d378438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377291, d378438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377291, d378438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377292 q = 0) : d378439 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377292, d378439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377292, d378439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d377350 q = 0) : d378497 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377350, d378497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377350, d378497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d377351 q = 0) : d378498 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377351, d378498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d377351, d378498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro39555 (p : Pattern) (selected : d377357 p = 0) : d378504 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377352 q = 0) : d378499 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377352, d378499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39554 q selected
    | true =>
      simp only [d377352, d378499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377353 q = 0) : d378500 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377353, d378500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377353, d378500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377296 q = 0) : d378443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377296, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39542 q selected
    | true =>
      simp only [d377296, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377297 q = 0) : d378444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377297, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377297, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377354 q = 0) : d378501 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377354, d378501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377354, d378501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377355 q = 0) : d378502 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377355, d378502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377355, d378502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377356 q = 0) : d378503 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377356, d378503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377356, d378503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377357 q = 0) : d378504 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377357, d378504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377357, d378504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39556 (p : Pattern) (selected : d377365 p = 0) : d378417 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d353344 q = 0) : d355080 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d353344, d355080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d353344, d355080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36614 q selected
  have h2 (q : Pattern) (selected : d377359 q = 0) : d378411 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d377359, d378411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377359, d378411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377360 q = 0) : d378412 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377360, d378412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377360, d378412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352045 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36614 q selected
    | true =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377361 q = 0) : d378413 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d377361, d378413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377361, d378413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377362 q = 0) : d378414 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377362, d378414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377362, d378414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377363 q = 0) : d378415 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d377363, d378415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377363, d378415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377364 q = 0) : d378416 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d377364, d378416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377364, d378416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377365 q = 0) : d378417 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d377365, d378417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377365, d378417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro39557 (p : Pattern) (selected : d377371 p = 0) : d378423 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377366 q = 0) : d378418 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377366, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39556 q selected
    | true =>
      simp only [d377366, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377367 q = 0) : d378419 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377367, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377367, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377368 q = 0) : d378420 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377368, d378420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377368, d378420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377369 q = 0) : d378421 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377369, d378421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377369, d378421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377370 q = 0) : d378422 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377370, d378422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377370, d378422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377371 q = 0) : d378423 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377371, d378423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377371, d378423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39558 (p : Pattern) (selected : d377373 p = 0) : d378425 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377366 q = 0) : d378418 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377366, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39556 q selected
    | true =>
      simp only [d377366, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377367 q = 0) : d378419 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377367, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377367, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377368 q = 0) : d378420 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377368, d378420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377368, d378420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377369 q = 0) : d378421 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377369, d378421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377369, d378421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377370 q = 0) : d378422 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377370, d378422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377370, d378422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377372 q = 0) : d378424 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377372, d378424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377372, d378424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377373 q = 0) : d378425 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377373, d378425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377373, d378425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro39559 (p : Pattern) (selected : d377377 p = 0) : d378429 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d353344 q = 0) : d355080 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d353344, d355080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d353344, d355080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36614 q selected
  have h2 (q : Pattern) (selected : d377359 q = 0) : d378411 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d377359, d378411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377359, d378411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377360 q = 0) : d378412 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377360, d378412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377360, d378412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352045 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36614 q selected
    | true =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377361 q = 0) : d378413 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d377361, d378413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377361, d378413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377362 q = 0) : d378414 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377362, d378414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377362, d378414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377363 q = 0) : d378415 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d377363, d378415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377363, d378415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377364 q = 0) : d378416 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d377364, d378416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377364, d378416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377377 q = 0) : d378429 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d377377, d378429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377377, d378429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro39560 (p : Pattern) (selected : d377383 p = 0) : d378435 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377366 q = 0) : d378418 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377366, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39556 q selected
    | true =>
      simp only [d377366, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377367 q = 0) : d378419 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377367, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377367, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377368 q = 0) : d378420 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377368, d378420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377368, d378420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377369 q = 0) : d378421 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377369, d378421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377369, d378421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377372 q = 0) : d378424 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377372, d378424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377372, d378424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377378 q = 0) : d378430 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377378, d378430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39559 q selected
    | true =>
      simp only [d377378, d378430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377379 q = 0) : d378431 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377379, d378431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377379, d378431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377380 q = 0) : d378432 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377380, d378432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377380, d378432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d377381 q = 0) : d378433 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377381, d378433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377381, d378433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d377382 q = 0) : d378434 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377382, d378434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377382, d378434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d377383 q = 0) : d378435 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377383, d378435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377383, d378435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39561 (p : Pattern) (selected : d377390 p = 0) : d378442 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377374 q = 0) : d378426 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377374, d378426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39557 q selected
    | true =>
      simp only [d377374, d378426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39558 q selected
  have h2 (q : Pattern) (selected : d377375 q = 0) : d378427 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377375, d378427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377375, d378427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377376 q = 0) : d378428 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377376, d378428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377376, d378428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377384 q = 0) : d378436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377384, d378436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39558 q selected
    | true =>
      simp only [d377384, d378436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39560 q selected
  have h5 (q : Pattern) (selected : d377385 q = 0) : d378437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377385, d378437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377385, d378437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377386 q = 0) : d378438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377386, d378438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377386, d378438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377387 q = 0) : d378439 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377387, d378439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377387, d378439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377388 q = 0) : d378440 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377388, d378440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377388, d378440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377389 q = 0) : d378441 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377389, d378441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377389, d378441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377390 q = 0) : d378442 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377390, d378442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377390, d378442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39562 (p : Pattern) (selected : d377394 p = 0) : d378446 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377384 q = 0) : d378436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377384, d378436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39558 q selected
    | true =>
      simp only [d377384, d378436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39560 q selected
  have h2 (q : Pattern) (selected : d377385 q = 0) : d378437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377385, d378437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377385, d378437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377386 q = 0) : d378438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377386, d378438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377386, d378438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377388 q = 0) : d378440 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377388, d378440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377388, d378440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377393 q = 0) : d378445 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377393, d378445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377393, d378445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377394 q = 0) : d378446 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377394, d378446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377394, d378446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39563 (p : Pattern) (selected : d377400 p = 0) : d378452 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377391 q = 0) : d378443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377391, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39561 q selected
    | true =>
      simp only [d377391, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377392 q = 0) : d378444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377392, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377392, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377395 q = 0) : d378447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377395, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39562 q selected
    | true =>
      simp only [d377395, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377396 q = 0) : d378448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377396, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377396, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377397 q = 0) : d378449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377397, d378449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377397, d378449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377398 q = 0) : d378450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377398, d378450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377398, d378450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377399 q = 0) : d378451 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377399, d378451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377399, d378451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377400 q = 0) : d378452 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377400, d378452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377400, d378452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39564 (p : Pattern) (selected : d377404 p = 0) : d378456 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377395 q = 0) : d378447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377395, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39562 q selected
    | true =>
      simp only [d377395, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377396 q = 0) : d378448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377396, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377396, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377401 q = 0) : d378453 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377401, d378453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377401, d378453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377402 q = 0) : d378454 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377402, d378454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377402, d378454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377403 q = 0) : d378455 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377403, d378455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377403, d378455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377404 q = 0) : d378456 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377404, d378456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377404, d378456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39565 (p : Pattern) (selected : d377407 p = 0) : d378507 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377271 q = 0) : d378418 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377271, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39537 q selected
    | true =>
      simp only [d377271, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377272 q = 0) : d378419 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377272, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377272, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377273 q = 0) : d378420 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377273, d378420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377273, d378420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377274 q = 0) : d378421 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377274, d378421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377274, d378421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377275 q = 0) : d378422 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377275, d378422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377275, d378422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377407 q = 0) : d378507 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377407, d378507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377407, d378507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39566 (p : Pattern) (selected : d377413 p = 0) : d378513 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377279 q = 0) : d378426 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377279, d378426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39538 q selected
    | true =>
      simp only [d377279, d378426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39539 q selected
  have h2 (q : Pattern) (selected : d377280 q = 0) : d378427 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377280, d378427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377280, d378427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377281 q = 0) : d378428 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377281, d378428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377281, d378428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377289 q = 0) : d378436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377289, d378436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39539 q selected
    | true =>
      simp only [d377289, d378436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39541 q selected
  have h5 (q : Pattern) (selected : d377290 q = 0) : d378437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377290, d378437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377290, d378437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377291 q = 0) : d378438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377291, d378438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377291, d378438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377292 q = 0) : d378439 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377292, d378439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377292, d378439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377408 q = 0) : d378508 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377408, d378508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39565 q selected
    | true =>
      simp only [d377408, d378508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377409 q = 0) : d378509 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377409, d378509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377409, d378509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377410 q = 0) : d378510 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377410, d378510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377410, d378510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377411 q = 0) : d378511 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377411, d378511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377411, d378511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d377412 q = 0) : d378512 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377412, d378512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377412, d378512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d377413 q = 0) : d378513 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377413, d378513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d377413, d378513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro39567 (p : Pattern) (selected : d377419 p = 0) : d378519 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377414 q = 0) : d378514 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377414, d378514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39566 q selected
    | true =>
      simp only [d377414, d378514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377415 q = 0) : d378515 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377415, d378515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377415, d378515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377416 q = 0) : d378516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377416, d378516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377416, d378516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377417 q = 0) : d378517 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377417, d378517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377417, d378517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377418 q = 0) : d378518 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377418, d378518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377418, d378518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377419 q = 0) : d378519 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377419, d378519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377419, d378519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39568 (p : Pattern) (selected : d377425 p = 0) : d378525 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377333 q = 0) : d378480 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377333, d378480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39550 q selected
    | true =>
      simp only [d377333, d378480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39551 q selected
  have h2 (q : Pattern) (selected : d377334 q = 0) : d378481 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377334, d378481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377334, d378481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377335 q = 0) : d378482 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377335, d378482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377335, d378482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377336 q = 0) : d378483 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377336, d378483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377336, d378483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377343 q = 0) : d378490 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377343, d378490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39552 q selected
    | true =>
      simp only [d377343, d378490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39553 q selected
  have h6 (q : Pattern) (selected : d377344 q = 0) : d378491 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377344, d378491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377344, d378491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377345 q = 0) : d378492 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377345, d378492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377345, d378492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377358 q = 0) : d378505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377358, d378505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39555 q selected
    | true =>
      simp only [d377358, d378505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39544 q selected
  have h9 (q : Pattern) (selected : d377405 q = 0) : d378457 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377405, d378457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39563 q selected
    | true =>
      simp only [d377405, d378457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39564 q selected
  have h10 (q : Pattern) (selected : d377406 q = 0) : d378506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377406, d378506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377406, d378506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377420 q = 0) : d378520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377420, d378520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39567 q selected
    | true =>
      simp only [d377420, d378520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d377421 q = 0) : d378521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377421, d378521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d377421, d378521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d377422 q = 0) : d378522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377422, d378522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377422, d378522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d377423 q = 0) : d378523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377423, d378523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377423, d378523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d377424 q = 0) : d378524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377424, d378524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377424, d378524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d377425 q = 0) : d378525 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377425, d378525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377425, d378525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro39569 (p : Pattern) (selected : d377426 p = 0) : d378526 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377296 q = 0) : d378443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377296, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39542 q selected
    | true =>
      simp only [d377296, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377297 q = 0) : d378444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377297, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377297, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377300 q = 0) : d378447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39543 q selected
    | true =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377301 q = 0) : d378448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377302 q = 0) : d378449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377302, d378449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377302, d378449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377303 q = 0) : d378450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377303, d378450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377303, d378450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377329 q = 0) : d378476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377329, d378476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377329, d378476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377426 q = 0) : d378526 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377426, d378526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377426, d378526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39570 (p : Pattern) (selected : d377427 p = 0) : d378527 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377300 q = 0) : d378447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39543 q selected
    | true =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377301 q = 0) : d378448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377306 q = 0) : d378453 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377306, d378453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377306, d378453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377307 q = 0) : d378454 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377307, d378454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377307, d378454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377331 q = 0) : d378478 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377331, d378478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377331, d378478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377427 q = 0) : d378527 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377427, d378527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377427, d378527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39571 (p : Pattern) (selected : d377432 p = 0) : d378532 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377296 q = 0) : d378443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377296, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39542 q selected
    | true =>
      simp only [d377296, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377297 q = 0) : d378444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377297, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377297, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377300 q = 0) : d378447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39543 q selected
    | true =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377301 q = 0) : d378448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377302 q = 0) : d378449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377302, d378449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377302, d378449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377337 q = 0) : d378484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377337, d378484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377337, d378484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377338 q = 0) : d378485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377338, d378485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377338, d378485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377432 q = 0) : d378532 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377432, d378532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377432, d378532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39572 (p : Pattern) (selected : d377433 p = 0) : d378533 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377300 q = 0) : d378447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39543 q selected
    | true =>
      simp only [d377300, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377301 q = 0) : d378448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377301, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377306 q = 0) : d378453 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377306, d378453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377306, d378453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377340 q = 0) : d378487 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377340, d378487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377340, d378487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377341 q = 0) : d378488 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377341, d378488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377341, d378488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377433 q = 0) : d378533 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377433, d378533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377433, d378533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39573 (p : Pattern) (selected : d377437 p = 0) : d378537 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377352 q = 0) : d378499 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377352, d378499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39554 q selected
    | true =>
      simp only [d377352, d378499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377353 q = 0) : d378500 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377353, d378500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377353, d378500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377296 q = 0) : d378443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377296, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39542 q selected
    | true =>
      simp only [d377296, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377297 q = 0) : d378444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377297, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377297, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377354 q = 0) : d378501 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377354, d378501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377354, d378501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377355 q = 0) : d378502 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377355, d378502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377355, d378502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377356 q = 0) : d378503 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377356, d378503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377356, d378503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377437 q = 0) : d378537 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377437, d378537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377437, d378537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39574 (p : Pattern) (selected : d377439 p = 0) : d378465 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377391 q = 0) : d378443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377391, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39561 q selected
    | true =>
      simp only [d377391, d378443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377392 q = 0) : d378444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377392, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377392, d378444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377395 q = 0) : d378447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377395, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39562 q selected
    | true =>
      simp only [d377395, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377396 q = 0) : d378448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377396, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377396, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377397 q = 0) : d378449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377397, d378449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377397, d378449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377398 q = 0) : d378450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377398, d378450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377398, d378450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377399 q = 0) : d378451 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377399, d378451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377399, d378451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377439 q = 0) : d378465 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377439, d378465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377439, d378465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39575 (p : Pattern) (selected : d377440 p = 0) : d378466 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377395 q = 0) : d378447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377395, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39562 q selected
    | true =>
      simp only [d377395, d378447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377396 q = 0) : d378448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377396, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377396, d378448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377401 q = 0) : d378453 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377401, d378453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377401, d378453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377402 q = 0) : d378454 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377402, d378454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377402, d378454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377403 q = 0) : d378455 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377403, d378455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377403, d378455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377440 q = 0) : d378466 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377440, d378466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377440, d378466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39576 (p : Pattern) (selected : d377443 p = 0) : d378540 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377414 q = 0) : d378514 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377414, d378514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39566 q selected
    | true =>
      simp only [d377414, d378514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377415 q = 0) : d378515 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377415, d378515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377415, d378515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377416 q = 0) : d378516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377416, d378516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377416, d378516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377417 q = 0) : d378517 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377417, d378517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377417, d378517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377418 q = 0) : d378518 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377418, d378518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377418, d378518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377443 q = 0) : d378540 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377443, d378540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377443, d378540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39577 (p : Pattern) (selected : d377449 p = 0) : d378546 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377333 q = 0) : d378480 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377333, d378480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39550 q selected
    | true =>
      simp only [d377333, d378480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39551 q selected
  have h2 (q : Pattern) (selected : d377334 q = 0) : d378481 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377334, d378481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377334, d378481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377335 q = 0) : d378482 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377335, d378482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377335, d378482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377336 q = 0) : d378483 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377336, d378483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377336, d378483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377343 q = 0) : d378490 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377343, d378490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39552 q selected
    | true =>
      simp only [d377343, d378490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39553 q selected
  have h6 (q : Pattern) (selected : d377344 q = 0) : d378491 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377344, d378491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377344, d378491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377345 q = 0) : d378492 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377345, d378492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377345, d378492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377358 q = 0) : d378505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377358, d378505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39555 q selected
    | true =>
      simp only [d377358, d378505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39544 q selected
  have h9 (q : Pattern) (selected : d377405 q = 0) : d378457 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377405, d378457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39563 q selected
    | true =>
      simp only [d377405, d378457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39564 q selected
  have h10 (q : Pattern) (selected : d377406 q = 0) : d378506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377406, d378506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377406, d378506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377420 q = 0) : d378520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377420, d378520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39567 q selected
    | true =>
      simp only [d377420, d378520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d377421 q = 0) : d378521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377421, d378521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d377421, d378521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d377422 q = 0) : d378522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377422, d378522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377422, d378522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d377423 q = 0) : d378523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377423, d378523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377423, d378523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d377424 q = 0) : d378524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377424, d378524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377424, d378524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d377428 q = 0) : d378528 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377428, d378528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39569 q selected
    | true =>
      simp only [d377428, d378528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39570 q selected
  have h17 (q : Pattern) (selected : d377429 q = 0) : d378529 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377429, d378529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377429, d378529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d377430 q = 0) : d378530 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377430, d378530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d377430, d378530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d377431 q = 0) : d378531 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377431, d378531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377431, d378531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d377434 q = 0) : d378534 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377434, d378534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39571 q selected
    | true =>
      simp only [d377434, d378534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39572 q selected
  have h21 (q : Pattern) (selected : d377435 q = 0) : d378535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377435, d378535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377435, d378535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d377436 q = 0) : d378536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377436, d378536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d377436, d378536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d377438 q = 0) : d378538 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377438, d378538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39573 q selected
    | true =>
      simp only [d377438, d378538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39547 q selected
  have h24 (q : Pattern) (selected : d377441 q = 0) : d378467 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377441, d378467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39574 q selected
    | true =>
      simp only [d377441, d378467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39575 q selected
  have h25 (q : Pattern) (selected : d377442 q = 0) : d378539 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377442, d378539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d377442, d378539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d377444 q = 0) : d378541 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377444, d378541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39576 q selected
    | true =>
      simp only [d377444, d378541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d377445 q = 0) : d378542 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377445, d378542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d377445, d378542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d377446 q = 0) : d378543 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377446, d378543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d377446, d378543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d377447 q = 0) : d378544 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377447, d378544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d377447, d378544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d377448 q = 0) : d378545 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377448, d378545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d377448, d378545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d377449 q = 0) : d378546 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377449, d378546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d377449, d378546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro39578 (p : Pattern) (selected : d377456 p = 0) : d378553 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377310 q = 0) : d378457 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377310, d378457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39544 q selected
    | true =>
      simp only [d377310, d378457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39545 q selected
  have h2 (q : Pattern) (selected : d377311 q = 0) : d378458 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377311, d378458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377311, d378458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377312 q = 0) : d378459 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377312, d378459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377312, d378459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377313 q = 0) : d378460 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377313, d378460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377313, d378460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377314 q = 0) : d378461 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377314, d378461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377314, d378461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377451 q = 0) : d378548 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377451, d378548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39545 q selected
    | true =>
      simp only [d377451, d378548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377452 q = 0) : d378549 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377452, d378549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377452, d378549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377453 q = 0) : d378550 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377453, d378550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377453, d378550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377454 q = 0) : d378551 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377454, d378551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377454, d378551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377455 q = 0) : d378552 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377455, d378552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377455, d378552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377456 q = 0) : d378553 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377456, d378553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377456, d378553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39579 (p : Pattern) (selected : d377462 p = 0) : d378559 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377451 q = 0) : d378548 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377451, d378548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39545 q selected
    | true =>
      simp only [d377451, d378548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377452 q = 0) : d378549 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377452, d378549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377452, d378549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377453 q = 0) : d378550 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377453, d378550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377453, d378550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377454 q = 0) : d378551 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377454, d378551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377454, d378551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377455 q = 0) : d378552 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377455, d378552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377455, d378552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377457 q = 0) : d378554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377457, d378554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39548 q selected
    | true =>
      simp only [d377457, d378554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377458 q = 0) : d378555 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377458, d378555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377458, d378555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377459 q = 0) : d378556 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377459, d378556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377459, d378556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377460 q = 0) : d378557 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377460, d378557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377460, d378557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377461 q = 0) : d378558 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377461, d378558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377461, d378558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377462 q = 0) : d378559 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377462, d378559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377462, d378559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39580 (p : Pattern) (selected : d377469 p = 0) : d378566 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377438 q = 0) : d378538 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377438, d378538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39573 q selected
    | true =>
      simp only [d377438, d378538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39547 q selected
  have h2 (q : Pattern) (selected : d377441 q = 0) : d378467 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377441, d378467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39574 q selected
    | true =>
      simp only [d377441, d378467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39575 q selected
  have h3 (q : Pattern) (selected : d377442 q = 0) : d378539 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377442, d378539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377442, d378539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377444 q = 0) : d378541 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377444, d378541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39576 q selected
    | true =>
      simp only [d377444, d378541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377445 q = 0) : d378542 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377445, d378542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377445, d378542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377446 q = 0) : d378543 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377446, d378543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377446, d378543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377467 q = 0) : d378564 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377467, d378564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377467, d378564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377468 q = 0) : d378565 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377468, d378565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377468, d378565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d377469 q = 0) : d378566 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377469, d378566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377469, d378566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro39581 (p : Pattern) (selected : d377471 p = 0) : d378568 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377457 q = 0) : d378554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377457, d378554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39548 q selected
    | true =>
      simp only [d377457, d378554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377458 q = 0) : d378555 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377458, d378555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377458, d378555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377459 q = 0) : d378556 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377459, d378556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377459, d378556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377460 q = 0) : d378557 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377460, d378557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377460, d378557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377461 q = 0) : d378558 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377461, d378558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377461, d378558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377471 q = 0) : d378568 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377471, d378568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377471, d378568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39582 (p : Pattern) (selected : d377482 p = 0) : d378579 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377477 q = 0) : d378574 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377477, d378574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377477, d378574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39537 q selected
  have h2 (q : Pattern) (selected : d377271 q = 0) : d378418 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377271, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39537 q selected
    | true =>
      simp only [d377271, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377478 q = 0) : d378575 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377478, d378575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377478, d378575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377272 q = 0) : d378419 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377272, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377272, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377479 q = 0) : d378576 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377479, d378576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377479, d378576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377480 q = 0) : d378577 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377480, d378577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377480, d378577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377481 q = 0) : d378578 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377481, d378578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377481, d378578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377482 q = 0) : d378579 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377482, d378579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377482, d378579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39583 (p : Pattern) (selected : d377487 p = 0) : d378584 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377477 q = 0) : d378574 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377477, d378574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377477, d378574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39537 q selected
  have h2 (q : Pattern) (selected : d377271 q = 0) : d378418 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377271, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39537 q selected
    | true =>
      simp only [d377271, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377478 q = 0) : d378575 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377478, d378575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377478, d378575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377272 q = 0) : d378419 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377272, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377272, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377479 q = 0) : d378576 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377479, d378576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377479, d378576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377480 q = 0) : d378577 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377480, d378577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377480, d378577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377481 q = 0) : d378578 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377481, d378578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377481, d378578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377486 q = 0) : d378583 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377486, d378583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377486, d378583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377487 q = 0) : d378584 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377487, d378584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377487, d378584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro39584 (p : Pattern) (selected : d377497 p = 0) : d378594 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377477 q = 0) : d378574 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377477, d378574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377477, d378574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39537 q selected
  have h2 (q : Pattern) (selected : d377271 q = 0) : d378418 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377271, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39537 q selected
    | true =>
      simp only [d377271, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377478 q = 0) : d378575 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377478, d378575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377478, d378575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377272 q = 0) : d378419 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377272, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377272, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377479 q = 0) : d378576 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377479, d378576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377479, d378576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377480 q = 0) : d378577 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377480, d378577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377480, d378577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377486 q = 0) : d378583 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377486, d378583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377486, d378583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377492 q = 0) : d378589 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377492, d378589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377492, d378589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39540 q selected
  have h9 (q : Pattern) (selected : d377283 q = 0) : d378430 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377283, d378430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39540 q selected
    | true =>
      simp only [d377283, d378430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d377493 q = 0) : d378590 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377493, d378590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377493, d378590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377284 q = 0) : d378431 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377284, d378431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377284, d378431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d377494 q = 0) : d378591 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377494, d378591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377494, d378591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d377495 q = 0) : d378592 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377495, d378592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d377495, d378592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d377496 q = 0) : d378593 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377496, d378593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377496, d378593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d377497 q = 0) : d378594 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377497, d378594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377497, d378594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro39585 (p : Pattern) (selected : d377503 p = 0) : d378600 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377483 q = 0) : d378580 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377483, d378580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377483, d378580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39582 q selected
  have h2 (q : Pattern) (selected : d377484 q = 0) : d378581 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377484, d378581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377484, d378581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377485 q = 0) : d378582 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377485, d378582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377485, d378582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377488 q = 0) : d378585 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377488, d378585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39582 q selected
    | true =>
      simp only [d377488, d378585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39583 q selected
  have h5 (q : Pattern) (selected : d377489 q = 0) : d378586 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377489, d378586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377489, d378586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377490 q = 0) : d378587 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377490, d378587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377490, d378587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377491 q = 0) : d378588 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377491, d378588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377491, d378588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377498 q = 0) : d378595 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377498, d378595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39583 q selected
    | true =>
      simp only [d377498, d378595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39584 q selected
  have h9 (q : Pattern) (selected : d377499 q = 0) : d378596 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377499, d378596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377499, d378596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377500 q = 0) : d378597 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377500, d378597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377500, d378597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377501 q = 0) : d378598 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377501, d378598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377501, d378598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d377502 q = 0) : d378599 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377502, d378599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377502, d378599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d377503 q = 0) : d378600 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377503, d378600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d377503, d378600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro39586 (p : Pattern) (selected : d377508 p = 0) : d378605 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377488 q = 0) : d378585 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377488, d378585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39582 q selected
    | true =>
      simp only [d377488, d378585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39583 q selected
  have h2 (q : Pattern) (selected : d377489 q = 0) : d378586 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377489, d378586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377489, d378586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377490 q = 0) : d378587 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377490, d378587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377490, d378587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377498 q = 0) : d378595 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377498, d378595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39583 q selected
    | true =>
      simp only [d377498, d378595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39584 q selected
  have h5 (q : Pattern) (selected : d377499 q = 0) : d378596 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377499, d378596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377499, d378596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377500 q = 0) : d378597 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377500, d378597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377500, d378597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377501 q = 0) : d378598 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377501, d378598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377501, d378598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377506 q = 0) : d378603 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377506, d378603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377506, d378603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377507 q = 0) : d378604 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377507, d378604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377507, d378604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377508 q = 0) : d378605 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377508, d378605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377508, d378605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39587 (p : Pattern) (selected : d377514 p = 0) : d378611 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377504 q = 0) : d378601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377504, d378601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39585 q selected
    | true =>
      simp only [d377504, d378601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377505 q = 0) : d378602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377505, d378602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377505, d378602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377509 q = 0) : d378606 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377509, d378606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39586 q selected
    | true =>
      simp only [d377509, d378606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377510 q = 0) : d378607 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377510, d378607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377510, d378607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377511 q = 0) : d378608 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377511, d378608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377511, d378608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377512 q = 0) : d378609 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377512, d378609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377512, d378609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377513 q = 0) : d378610 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377513, d378610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377513, d378610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377514 q = 0) : d378611 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377514, d378611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377514, d378611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39588 (p : Pattern) (selected : d377516 p = 0) : d378613 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377498 q = 0) : d378595 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377498, d378595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39583 q selected
    | true =>
      simp only [d377498, d378595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39584 q selected
  have h2 (q : Pattern) (selected : d377499 q = 0) : d378596 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377499, d378596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377499, d378596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377500 q = 0) : d378597 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377500, d378597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377500, d378597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377506 q = 0) : d378603 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377506, d378603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377506, d378603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377515 q = 0) : d378612 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377515, d378612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377515, d378612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377516 q = 0) : d378613 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377516, d378613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377516, d378613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39589 (p : Pattern) (selected : d377522 p = 0) : d378619 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377509 q = 0) : d378606 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377509, d378606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39586 q selected
    | true =>
      simp only [d377509, d378606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377510 q = 0) : d378607 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377510, d378607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377510, d378607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377517 q = 0) : d378614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377517, d378614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39588 q selected
    | true =>
      simp only [d377517, d378614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377518 q = 0) : d378615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377518, d378615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377518, d378615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377519 q = 0) : d378616 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377519, d378616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377519, d378616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377520 q = 0) : d378617 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377520, d378617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377520, d378617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377521 q = 0) : d378618 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377521, d378618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377521, d378618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377522 q = 0) : d378619 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377522, d378619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377522, d378619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39590 (p : Pattern) (selected : d377529 p = 0) : d378579 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377524 q = 0) : d378574 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377524, d378574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377524, d378574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39556 q selected
  have h2 (q : Pattern) (selected : d377366 q = 0) : d378418 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377366, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39556 q selected
    | true =>
      simp only [d377366, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377525 q = 0) : d378575 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377525, d378575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377525, d378575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377367 q = 0) : d378419 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377367, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377367, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377526 q = 0) : d378576 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377526, d378576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377526, d378576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377527 q = 0) : d378577 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377527, d378577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377527, d378577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377528 q = 0) : d378578 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377528, d378578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377528, d378578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377529 q = 0) : d378579 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377529, d378579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377529, d378579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39591 (p : Pattern) (selected : d377531 p = 0) : d378584 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377524 q = 0) : d378574 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377524, d378574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377524, d378574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39556 q selected
  have h2 (q : Pattern) (selected : d377366 q = 0) : d378418 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377366, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39556 q selected
    | true =>
      simp only [d377366, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377525 q = 0) : d378575 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377525, d378575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377525, d378575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377367 q = 0) : d378419 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377367, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377367, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377526 q = 0) : d378576 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377526, d378576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377526, d378576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377527 q = 0) : d378577 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377527, d378577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377527, d378577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377528 q = 0) : d378578 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377528, d378578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377528, d378578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377530 q = 0) : d378583 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377530, d378583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377530, d378583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377531 q = 0) : d378584 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377531, d378584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377531, d378584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro39592 (p : Pattern) (selected : d377540 p = 0) : d378594 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377524 q = 0) : d378574 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377524, d378574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377524, d378574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39556 q selected
  have h2 (q : Pattern) (selected : d377366 q = 0) : d378418 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377366, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39556 q selected
    | true =>
      simp only [d377366, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377525 q = 0) : d378575 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377525, d378575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377525, d378575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377367 q = 0) : d378419 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377367, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377367, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377526 q = 0) : d378576 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377526, d378576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377526, d378576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377527 q = 0) : d378577 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377527, d378577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377527, d378577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377530 q = 0) : d378583 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377530, d378583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377530, d378583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377535 q = 0) : d378589 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377535, d378589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377535, d378589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39559 q selected
  have h9 (q : Pattern) (selected : d377378 q = 0) : d378430 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377378, d378430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39559 q selected
    | true =>
      simp only [d377378, d378430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d377536 q = 0) : d378590 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377536, d378590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377536, d378590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377379 q = 0) : d378431 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377379, d378431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377379, d378431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d377537 q = 0) : d378591 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377537, d378591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377537, d378591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d377538 q = 0) : d378592 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377538, d378592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d377538, d378592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d377539 q = 0) : d378593 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377539, d378593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377539, d378593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d377540 q = 0) : d378594 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377540, d378594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377540, d378594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro39593 (p : Pattern) (selected : d377547 p = 0) : d378605 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377532 q = 0) : d378585 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377532, d378585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39590 q selected
    | true =>
      simp only [d377532, d378585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39591 q selected
  have h2 (q : Pattern) (selected : d377533 q = 0) : d378586 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377533, d378586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377533, d378586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377534 q = 0) : d378587 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377534, d378587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377534, d378587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377541 q = 0) : d378595 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377541, d378595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39591 q selected
    | true =>
      simp only [d377541, d378595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39592 q selected
  have h5 (q : Pattern) (selected : d377542 q = 0) : d378596 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377542, d378596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377542, d378596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377543 q = 0) : d378597 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377543, d378597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377543, d378597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377544 q = 0) : d378598 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377544, d378598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377544, d378598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377545 q = 0) : d378603 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377545, d378603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377545, d378603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377546 q = 0) : d378604 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377546, d378604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377546, d378604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377547 q = 0) : d378605 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377547, d378605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377547, d378605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39594 (p : Pattern) (selected : d377551 p = 0) : d378613 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377541 q = 0) : d378595 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377541, d378595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39591 q selected
    | true =>
      simp only [d377541, d378595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39592 q selected
  have h2 (q : Pattern) (selected : d377542 q = 0) : d378596 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377542, d378596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377542, d378596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377543 q = 0) : d378597 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377543, d378597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377543, d378597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377545 q = 0) : d378603 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377545, d378603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377545, d378603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377550 q = 0) : d378612 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377550, d378612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377550, d378612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377551 q = 0) : d378613 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377551, d378613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377551, d378613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39595 (p : Pattern) (selected : d377557 p = 0) : d378619 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377548 q = 0) : d378606 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377548, d378606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39593 q selected
    | true =>
      simp only [d377548, d378606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377549 q = 0) : d378607 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377549, d378607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377549, d378607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377552 q = 0) : d378614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377552, d378614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39594 q selected
    | true =>
      simp only [d377552, d378614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377553 q = 0) : d378615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377553, d378615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377553, d378615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377554 q = 0) : d378616 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377554, d378616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377554, d378616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377555 q = 0) : d378617 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377555, d378617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377555, d378617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377556 q = 0) : d378618 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377556, d378618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377556, d378618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377557 q = 0) : d378619 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377557, d378619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377557, d378619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39596 (p : Pattern) (selected : d377563 p = 0) : d378626 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377558 q = 0) : d378621 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d377558, d378621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39381 q selected
    | true =>
      simp only [d377558, d378621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36614 q selected
  have h2 (q : Pattern) (selected : d377559 q = 0) : d378622 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d377559, d378622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377559, d378622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377560 q = 0) : d378623 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377560, d378623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377560, d378623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352045 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36614 q selected
    | true =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377361 q = 0) : d378413 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d377361, d378413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377361, d378413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377362 q = 0) : d378414 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377362, d378414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377362, d378414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377561 q = 0) : d378624 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d377561, d378624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377561, d378624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377562 q = 0) : d378625 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d377562, d378625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377562, d378625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377563 q = 0) : d378626 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d377563, d378626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377563, d378626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro39597 (p : Pattern) (selected : d377569 p = 0) : d378632 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377524 q = 0) : d378574 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377524, d378574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377524, d378574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39556 q selected
  have h2 (q : Pattern) (selected : d377366 q = 0) : d378418 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377366, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39556 q selected
    | true =>
      simp only [d377366, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377525 q = 0) : d378575 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377525, d378575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377525, d378575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377367 q = 0) : d378419 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377367, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377367, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377526 q = 0) : d378576 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377526, d378576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377526, d378576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377527 q = 0) : d378577 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377527, d378577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377527, d378577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377530 q = 0) : d378583 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377530, d378583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377530, d378583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377535 q = 0) : d378589 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377535, d378589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377535, d378589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39559 q selected
  have h9 (q : Pattern) (selected : d377378 q = 0) : d378430 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377378, d378430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39559 q selected
    | true =>
      simp only [d377378, d378430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d377536 q = 0) : d378590 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377536, d378590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377536, d378590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377564 q = 0) : d378627 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377564, d378627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39596 q selected
    | true =>
      simp only [d377564, d378627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d377565 q = 0) : d378628 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377565, d378628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d377565, d378628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d377566 q = 0) : d378629 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377566, d378629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377566, d378629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d377567 q = 0) : d378630 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377567, d378630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377567, d378630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d377568 q = 0) : d378631 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377568, d378631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d377568, d378631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d377569 q = 0) : d378632 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377569, d378632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377569, d378632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro39598 (p : Pattern) (selected : d377575 p = 0) : d378638 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377570 q = 0) : d378633 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377570, d378633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39591 q selected
    | true =>
      simp only [d377570, d378633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39597 q selected
  have h2 (q : Pattern) (selected : d377571 q = 0) : d378634 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377571, d378634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377571, d378634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377572 q = 0) : d378635 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377572, d378635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377572, d378635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377573 q = 0) : d378636 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377573, d378636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377573, d378636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377574 q = 0) : d378637 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377574, d378637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377574, d378637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377575 q = 0) : d378638 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377575, d378638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377575, d378638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39599 (p : Pattern) (selected : d377581 p = 0) : d378644 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377576 q = 0) : d378639 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377576, d378639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39598 q selected
    | true =>
      simp only [d377576, d378639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377577 q = 0) : d378640 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377577, d378640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377577, d378640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377578 q = 0) : d378641 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377578, d378641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377578, d378641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377579 q = 0) : d378642 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377579, d378642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377579, d378642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377580 q = 0) : d378643 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377580, d378643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377580, d378643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377581 q = 0) : d378644 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377581, d378644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377581, d378644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39600 (p : Pattern) (selected : d377584 p = 0) : d378647 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377477 q = 0) : d378574 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377477, d378574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377477, d378574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39537 q selected
  have h2 (q : Pattern) (selected : d377271 q = 0) : d378418 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377271, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39537 q selected
    | true =>
      simp only [d377271, d378418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377478 q = 0) : d378575 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377478, d378575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377478, d378575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377272 q = 0) : d378419 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377272, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377272, d378419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377479 q = 0) : d378576 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377479, d378576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377479, d378576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377480 q = 0) : d378577 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377480, d378577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377480, d378577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377481 q = 0) : d378578 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377481, d378578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377481, d378578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377584 q = 0) : d378647 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377584, d378647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377584, d378647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39601 (p : Pattern) (selected : d377590 p = 0) : d378653 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377488 q = 0) : d378585 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377488, d378585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39582 q selected
    | true =>
      simp only [d377488, d378585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39583 q selected
  have h2 (q : Pattern) (selected : d377489 q = 0) : d378586 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377489, d378586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377489, d378586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377490 q = 0) : d378587 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377490, d378587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377490, d378587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377498 q = 0) : d378595 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377498, d378595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39583 q selected
    | true =>
      simp only [d377498, d378595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39584 q selected
  have h5 (q : Pattern) (selected : d377499 q = 0) : d378596 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377499, d378596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377499, d378596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377500 q = 0) : d378597 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377500, d378597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377500, d378597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377501 q = 0) : d378598 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377501, d378598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377501, d378598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377585 q = 0) : d378648 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377585, d378648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39600 q selected
    | true =>
      simp only [d377585, d378648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377586 q = 0) : d378649 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377586, d378649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377586, d378649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377587 q = 0) : d378650 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377587, d378650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377587, d378650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377588 q = 0) : d378651 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377588, d378651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377588, d378651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d377589 q = 0) : d378652 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377589, d378652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377589, d378652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d377590 q = 0) : d378653 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377590, d378653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d377590, d378653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro39602 (p : Pattern) (selected : d377596 p = 0) : d378659 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377591 q = 0) : d378654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377591, d378654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39601 q selected
    | true =>
      simp only [d377591, d378654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377592 q = 0) : d378655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377592, d378655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377592, d378655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377593 q = 0) : d378656 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377593, d378656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377593, d378656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377594 q = 0) : d378657 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377594, d378657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377594, d378657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377595 q = 0) : d378658 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377595, d378658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377595, d378658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377596 q = 0) : d378659 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377596, d378659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377596, d378659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39603 (p : Pattern) (selected : d377602 p = 0) : d378665 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377523 q = 0) : d378620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377523, d378620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39587 q selected
    | true =>
      simp only [d377523, d378620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39589 q selected
  have h2 (q : Pattern) (selected : d377582 q = 0) : d378645 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377582, d378645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39595 q selected
    | true =>
      simp only [d377582, d378645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39599 q selected
  have h3 (q : Pattern) (selected : d377583 q = 0) : d378646 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377583, d378646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377583, d378646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377597 q = 0) : d378660 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377597, d378660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39602 q selected
    | true =>
      simp only [d377597, d378660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377598 q = 0) : d378661 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377598, d378661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377598, d378661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377599 q = 0) : d378662 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377599, d378662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377599, d378662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377600 q = 0) : d378663 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377600, d378663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377600, d378663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377601 q = 0) : d378664 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377601, d378664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377601, d378664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d377602 q = 0) : d378665 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377602, d378665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377602, d378665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro39604 (p : Pattern) (selected : d377607 p = 0) : d378670 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377517 q = 0) : d378614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377517, d378614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39588 q selected
    | true =>
      simp only [d377517, d378614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377518 q = 0) : d378615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377518, d378615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377518, d378615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377604 q = 0) : d378667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377604, d378667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377604, d378667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377605 q = 0) : d378668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377605, d378668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377605, d378668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377606 q = 0) : d378669 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377606, d378669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377606, d378669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377607 q = 0) : d378670 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377607, d378670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377607, d378670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39605 (p : Pattern) (selected : d377613 p = 0) : d378676 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377608 q = 0) : d378671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377608, d378671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39604 q selected
    | true =>
      simp only [d377608, d378671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377609 q = 0) : d378672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377609, d378672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377609, d378672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377610 q = 0) : d378673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377610, d378673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377610, d378673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377611 q = 0) : d378674 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377611, d378674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377611, d378674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377612 q = 0) : d378675 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377612, d378675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377612, d378675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377613 q = 0) : d378676 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377613, d378676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377613, d378676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39606 (p : Pattern) (selected : d377619 p = 0) : d378682 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377316 q = 0) : d378463 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377316, d378463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377316, d378463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39546 q selected
  have h2 (q : Pattern) (selected : d377317 q = 0) : d378464 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d377317, d378464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377317, d378464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377326 q = 0) : d378473 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377326, d378473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39546 q selected
    | true =>
      simp only [d377326, d378473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39549 q selected
  have h4 (q : Pattern) (selected : d377327 q = 0) : d378474 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d377327, d378474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377327, d378474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377328 q = 0) : d378475 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d377328, d378475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377328, d378475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377450 q = 0) : d378547 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377450, d378547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39568 q selected
    | true =>
      simp only [d377450, d378547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39577 q selected
  have h7 (q : Pattern) (selected : d377463 q = 0) : d378560 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377463, d378560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39578 q selected
    | true =>
      simp only [d377463, d378560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39579 q selected
  have h8 (q : Pattern) (selected : d377464 q = 0) : d378561 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d377464, d378561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377464, d378561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d377465 q = 0) : d378562 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d377465, d378562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377465, d378562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d377466 q = 0) : d378563 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d377466, d378563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377466, d378563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377470 q = 0) : d378567 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377470, d378567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377470, d378567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39580 q selected
  have h12 (q : Pattern) (selected : d377472 q = 0) : d378569 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377472, d378569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377472, d378569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39581 q selected
  have h13 (q : Pattern) (selected : d377473 q = 0) : d378570 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d377473, d378570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d377473, d378570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d377474 q = 0) : d378571 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d377474, d378571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377474, d378571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d377475 q = 0) : d378572 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d377475, d378572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d377475, d378572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d377476 q = 0) : d378573 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d377476, d378573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377476, d378573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d377603 q = 0) : d378666 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377603, d378666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377603, d378666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39603 q selected
  have h18 (q : Pattern) (selected : d377614 q = 0) : d378677 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377614, d378677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377614, d378677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39605 q selected
  have h19 (q : Pattern) (selected : d377615 q = 0) : d378678 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d377615, d378678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d377615, d378678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d377616 q = 0) : d378679 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d377616, d378679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d377616, d378679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d377617 q = 0) : d378680 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d377617, d378680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d377617, d378680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d377618 q = 0) : d378681 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d377618, d378681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d377618, d378681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d377619 q = 0) : d378682 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d377619, d378682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d377619, d378682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro39607 (p : Pattern) (selected : d377625 p = 0) : d378688 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377620 q = 0) : d378683 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d377620, d378683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377620, d378683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39606 q selected
  have h2 (q : Pattern) (selected : d377621 q = 0) : d378684 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d377621, d378684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377621, d378684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377622 q = 0) : d378685 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d377622, d378685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377622, d378685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377623 q = 0) : d378686 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d377623, d378686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377623, d378686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377624 q = 0) : d378687 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d377624, d378687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377624, d378687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377625 q = 0) : d378688 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d377625, d378688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377625, d378688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39608 (p : Pattern) (selected : d377631 p = 0) : d378694 p = 1 := by
  have h0 (q : Pattern) (selected : d376577 q = 0) : d377913 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d376577, d377913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39370 q selected
    | true =>
      simp only [d376577, d377913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39405 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d376892 q = 0) : d378150 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d376892, d378150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376892, d378150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39465 q selected
  have h3 (q : Pattern) (selected : d376893 q = 0) : d378151 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d376893, d378151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376893, d378151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377260 q = 0) : d378407 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d377260, d378407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377260, d378407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39536 q selected
  have h5 (q : Pattern) (selected : d377261 q = 0) : d378408 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d377261, d378408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377261, d378408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377262 q = 0) : d378409 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d377262, d378409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377262, d378409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377263 q = 0) : d378410 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d377263, d378410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377263, d378410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d377626 q = 0) : d378689 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d377626, d378689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377626, d378689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39607 q selected
  have h9 (q : Pattern) (selected : d377627 q = 0) : d378690 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d377627, d378690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377627, d378690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377628 q = 0) : d378691 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d377628, d378691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377628, d378691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377629 q = 0) : d378692 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d377629, d378692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377629, d378692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d377630 q = 0) : d378693 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d377630, d378693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377630, d378693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d377631 q = 0) : d378694 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d377631, d378694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d377631, d378694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h13 p selected
theorem eqIntro39609 (p : Pattern) (selected : d377637 p = 0) : d378700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377632 q = 0) : d378695 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d377632, d378695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39608 q selected
    | true =>
      simp only [d377632, d378695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377633 q = 0) : d378696 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d377633, d378696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377633, d378696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377634 q = 0) : d378697 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d377634, d378697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377634, d378697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377635 q = 0) : d378698 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d377635, d378698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377635, d378698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377636 q = 0) : d378699 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d377636, d378699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377636, d378699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377637 q = 0) : d378700 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d377637, d378700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377637, d378700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39610 (p : Pattern) (selected : d377643 p = 0) : d378706 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377638 q = 0) : d378701 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d377638, d378701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39609 q selected
    | true =>
      simp only [d377638, d378701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377639 q = 0) : d378702 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d377639, d378702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377639, d378702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377640 q = 0) : d378703 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d377640, d378703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377640, d378703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377641 q = 0) : d378704 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d377641, d378704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377641, d378704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377642 q = 0) : d378705 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d377642, d378705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377642, d378705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377643 q = 0) : d378706 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d377643, d378706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377643, d378706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39611 (p : Pattern) (selected : d377649 p = 0) : d378712 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377644 q = 0) : d378707 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d377644, d378707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39610 q selected
    | true =>
      simp only [d377644, d378707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377645 q = 0) : d378708 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d377645, d378708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377645, d378708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377646 q = 0) : d378709 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d377646, d378709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377646, d378709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377647 q = 0) : d378710 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d377647, d378710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377647, d378710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377648 q = 0) : d378711 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d377648, d378711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377648, d378711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377649 q = 0) : d378712 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d377649, d378712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377649, d378712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39612 (p : Pattern) (selected : d377655 p = 0) : d378718 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377650 q = 0) : d378713 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d377650, d378713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39611 q selected
    | true =>
      simp only [d377650, d378713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377651 q = 0) : d378714 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d377651, d378714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377651, d378714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377652 q = 0) : d378715 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d377652, d378715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377652, d378715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377653 q = 0) : d378716 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d377653, d378716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377653, d378716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377654 q = 0) : d378717 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d377654, d378717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377654, d378717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377655 q = 0) : d378718 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d377655, d378718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377655, d378718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39613 (p : Pattern) (selected : d377661 p = 0) : d378724 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377656 q = 0) : d378719 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d377656, d378719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39612 q selected
    | true =>
      simp only [d377656, d378719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377657 q = 0) : d378720 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d377657, d378720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377657, d378720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377658 q = 0) : d378721 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d377658, d378721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377658, d378721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377659 q = 0) : d378722 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d377659, d378722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377659, d378722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377660 q = 0) : d378723 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d377660, d378723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377660, d378723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377661 q = 0) : d378724 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d377661, d378724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377661, d378724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39614 (p : Pattern) (selected : d377667 p = 0) : d378730 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377662 q = 0) : d378725 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d377662, d378725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39613 q selected
    | true =>
      simp only [d377662, d378725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377663 q = 0) : d378726 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d377663, d378726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377663, d378726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377664 q = 0) : d378727 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d377664, d378727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377664, d378727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377665 q = 0) : d378728 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d377665, d378728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377665, d378728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377666 q = 0) : d378729 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d377666, d378729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377666, d378729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377667 q = 0) : d378730 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d377667, d378730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377667, d378730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39615 (p : Pattern) (selected : d377673 p = 0) : d378736 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d377668 q = 0) : d378731 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d377668, d378731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39614 q selected
    | true =>
      simp only [d377668, d378731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377669 q = 0) : d378732 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d377669, d378732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377669, d378732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377670 q = 0) : d378733 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d377670, d378733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377670, d378733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377671 q = 0) : d378734 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d377671, d378734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377671, d378734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377672 q = 0) : d378735 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d377672, d378735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377672, d378735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377673 q = 0) : d378736 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d377673, d378736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377673, d378736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39616 (p : Pattern) (selected : d376321 p = 1) : d378741 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d352006 q = 1) : d352006 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d352012 q = 1) : d352012 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d376316 q = 1) : d376316 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d352069 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36994 q selected
    | true =>
      simp only [d352069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376317 q = 1) : d378737 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376317, d378737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376317, d378737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351929 q = 1) : d351929 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d376318 q = 1) : d378738 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376318, d378738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376318, d378738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376319 q = 1) : d378739 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376319, d378739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376319, d378739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376320 q = 1) : d378740 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376320, d378740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376320, d378740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376321 q = 1) : d378741 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376321, d378741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376321, d378741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro39617 (p : Pattern) (selected : d376328 p = 1) : d378746 p = 1 := by
  have h0 (q : Pattern) (selected : d352006 q = 1) : d352006 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d352012 q = 1) : d352012 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d376316 q = 1) : d376316 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d352069 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36994 q selected
    | true =>
      simp only [d352069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376317 q = 1) : d378737 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376317, d378737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376317, d378737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351929 q = 1) : d351929 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d376318 q = 1) : d378738 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376318, d378738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376318, d378738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376319 q = 1) : d378739 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376319, d378739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376319, d378739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376320 q = 1) : d378740 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376320, d378740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376320, d378740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352079 q = 1) : d352079 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d352083 q = 1) : d352083 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d376323 q = 1) : d376323 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d352087 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36996 q selected
    | true =>
      simp only [d352087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d376324 q = 1) : d378742 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376324, d378742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376324, d378742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d351936 q = 1) : d351936 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d376325 q = 1) : d378743 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376325, d378743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d376325, d378743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d376326 q = 1) : d378744 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376326, d378744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d376326, d378744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d376327 q = 1) : d378745 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376327, d378745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376327, d378745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d376328 q = 1) : d378746 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376328, d378746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376328, d378746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro39618 (p : Pattern) (selected : d376335 p = 1) : d378753 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376323 q = 1) : d376323 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d352087 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36996 q selected
    | true =>
      simp only [d352087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376324 q = 1) : d378742 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376324, d378742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376324, d378742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351936 q = 1) : d351936 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d376325 q = 1) : d378743 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376325, d378743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376325, d378743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376333 q = 1) : d378751 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376333, d378751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376333, d378751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376334 q = 1) : d378752 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376334, d378752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376334, d378752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376335 q = 1) : d378753 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376335, d378753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376335, d378753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39619 (p : Pattern) (selected : d376364 p = 1) : d378763 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376359 q = 1) : d376359 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d352144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37001 q selected
    | true =>
      simp only [d352144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376360 q = 1) : d378759 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376360, d378759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376360, d378759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351970 q = 1) : d351970 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d376361 q = 1) : d378760 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376361, d378760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376361, d378760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376362 q = 1) : d378761 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376362, d378761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376362, d378761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376363 q = 1) : d378762 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376363, d378762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376363, d378762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376364 q = 1) : d378763 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376364, d378763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376364, d378763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39620 (p : Pattern) (selected : d376370 p = 1) : d378769 p = 1 := by
  have h0 (q : Pattern) (selected : d352000 q = 1) : d352000 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376329 q = 1) : d378747 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376329, d378747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39616 q selected
    | true =>
      simp only [d376329, d378747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39617 q selected
  have h2 (q : Pattern) (selected : d352095 q = 1) : d352095 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d376330 q = 1) : d378748 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376330, d378748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376330, d378748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d376331 q = 1) : d378749 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376331, d378749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376331, d378749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376332 q = 1) : d378750 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d376332, d378750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376332, d378750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376336 q = 1) : d378754 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376336, d378754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376336, d378754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39618 q selected
  have h8 (q : Pattern) (selected : d376337 q = 1) : d378755 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376337, d378755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376337, d378755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d376338 q = 1) : d378756 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376338, d378756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376338, d378756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d376339 q = 1) : d378757 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d376339, d378757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376339, d378757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d376340 q = 1) : d378758 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d376340, d378758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376340, d378758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d376365 q = 1) : d378764 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376365, d378764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376365, d378764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39619 q selected
  have h13 (q : Pattern) (selected : d376366 q = 1) : d378765 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376366, d378765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376366, d378765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d376367 q = 1) : d378766 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376367, d378766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376367, d378766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d376368 q = 1) : d378767 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d376368, d378767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d376368, d378767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d376369 q = 1) : d378768 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d376369, d378768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d376369, d378768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d376370 q = 1) : d378769 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d376370, d378769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d376370, d378769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro39621 (p : Pattern) (selected : d376376 p = 1) : d378775 p = 1 := by
  have h0 (q : Pattern) (selected : d351985 q = 1) : d351985 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d376371 q = 1) : d378770 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d376371, d378770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376371, d378770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39620 q selected
  have h3 (q : Pattern) (selected : d376372 q = 1) : d378771 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d376372, d378771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376372, d378771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376373 q = 1) : d378772 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d376373, d378772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376373, d378772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376374 q = 1) : d378773 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d376374, d378773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376374, d378773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376375 q = 1) : d378774 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d376375, d378774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376375, d378774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376376 q = 1) : d378775 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d376376, d378775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376376, d378775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro39622 (p : Pattern) (selected : d376439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d352041 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d352041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352042 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d352042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376438 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d376438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352043 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d352043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376439 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d376439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39623 (p : Pattern) (selected : d376445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376440 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39622 q selected
    | true =>
      simp only [d376440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376441 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352045 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36990 q selected
    | true =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352046 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376442 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352047 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376443 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376444 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352048 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d352049 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376445 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d376445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39624 (p : Pattern) (selected : d376451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376446 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39623 q selected
    | true =>
      simp only [d376446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376447 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376448 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376449 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36991 q selected
    | true =>
      simp only [d352051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352052 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352053 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352054 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376450 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352055 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376451 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39625 (p : Pattern) (selected : d376457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376452 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39624 q selected
    | true =>
      simp only [d376452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36992 q selected
  have h2 (q : Pattern) (selected : d376453 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376454 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352057 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36992 q selected
    | true =>
      simp only [d352057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352058 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352059 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376455 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352060 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376456 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376457 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39626 (p : Pattern) (selected : d376463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39625 q selected
    | true =>
      simp only [d376458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352063 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36993 q selected
    | true =>
      simp only [d352063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352064 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376461 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376462 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376463 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39627 (p : Pattern) (selected : d376475 p = 1) : d378780 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376397 q = 1) : d376397 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d376403 q = 1) : d376403 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d376437 q = 1) : d376437 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d376464 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39626 q selected
    | true =>
      simp only [d376464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36994 q selected
  have h5 (q : Pattern) (selected : d376465 q = 1) : d378776 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376465, d378776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376465, d378776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376471 q = 1) : d376471 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d376472 q = 1) : d378777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376472, d378777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376472, d378777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376473 q = 1) : d378778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376473, d378778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376473, d378778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376474 q = 1) : d378779 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376474, d378779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376474, d378779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376475 q = 1) : d378780 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376475, d378780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376475, d378780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro39628 (p : Pattern) (selected : d376487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39625 q selected
    | true =>
      simp only [d376458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352063 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36993 q selected
    | true =>
      simp only [d352063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352064 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376461 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376462 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39629 (p : Pattern) (selected : d376496 p = 1) : d378785 p = 1 := by
  have h0 (q : Pattern) (selected : d376397 q = 1) : d376397 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376403 q = 1) : d376403 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d376437 q = 1) : d376437 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d376464 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39626 q selected
    | true =>
      simp only [d376464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36994 q selected
  have h4 (q : Pattern) (selected : d376465 q = 1) : d378776 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376465, d378776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376465, d378776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376471 q = 1) : d376471 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d376472 q = 1) : d378777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376472, d378777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376472, d378777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376473 q = 1) : d378778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376473, d378778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376473, d378778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376474 q = 1) : d378779 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376474, d378779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376474, d378779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376480 q = 1) : d376480 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d376484 q = 1) : d376484 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d376486 q = 1) : d376486 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d376488 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39628 q selected
    | true =>
      simp only [d376488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36996 q selected
  have h13 (q : Pattern) (selected : d376489 q = 1) : d378781 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376489, d378781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d376489, d378781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d376492 q = 1) : d376492 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d376493 q = 1) : d378782 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376493, d378782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376493, d378782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d376494 q = 1) : d378783 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376494, d378783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376494, d378783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d376495 q = 1) : d378784 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376495, d378784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376495, d378784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d376496 q = 1) : d378785 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376496, d378785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376496, d378785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro39630 (p : Pattern) (selected : d376505 p = 1) : d378792 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376486 q = 1) : d376486 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d376488 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39628 q selected
    | true =>
      simp only [d376488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36996 q selected
  have h3 (q : Pattern) (selected : d376489 q = 1) : d378781 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376489, d378781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376489, d378781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376492 q = 1) : d376492 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d376493 q = 1) : d378782 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376493, d378782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376493, d378782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376503 q = 1) : d378790 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376503, d378790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376503, d378790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376504 q = 1) : d378791 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376504, d378791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376504, d378791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376505 q = 1) : d378792 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376505, d378792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376505, d378792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39631 (p : Pattern) (selected : d376540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376535 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39623 q selected
  have h2 (q : Pattern) (selected : d376446 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39623 q selected
    | true =>
      simp only [d376446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376536 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376447 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376537 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376538 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352126 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36991 q selected
  have h8 (q : Pattern) (selected : d352051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36991 q selected
    | true =>
      simp only [d352051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352127 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352052 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352128 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d352129 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d352129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d376539 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d352130 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d352130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d376540 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro39632 (p : Pattern) (selected : d376546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376541 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39631 q selected
    | true =>
      simp only [d376541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36999 q selected
  have h2 (q : Pattern) (selected : d376542 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376543 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352132 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36999 q selected
    | true =>
      simp only [d352132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352133 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352134 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376544 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352135 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376545 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376546 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39633 (p : Pattern) (selected : d376552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39632 q selected
    | true =>
      simp only [d376547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352138 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37000 q selected
    | true =>
      simp only [d352138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352139 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376549 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376550 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376551 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376552 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39634 (p : Pattern) (selected : d376564 p = 1) : d378802 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376534 q = 1) : d376534 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d376553 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39633 q selected
    | true =>
      simp only [d376553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37001 q selected
  have h3 (q : Pattern) (selected : d376554 q = 1) : d378798 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376554, d378798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376554, d378798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376560 q = 1) : d376560 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d376561 q = 1) : d378799 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376561, d378799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376561, d378799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376562 q = 1) : d378800 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376562, d378800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376562, d378800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376563 q = 1) : d378801 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376563, d378801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376563, d378801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376564 q = 1) : d378802 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376564, d378802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376564, d378802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39635 (p : Pattern) (selected : d376570 p = 1) : d378808 p = 1 := by
  have h0 (q : Pattern) (selected : d376391 q = 1) : d376391 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376497 q = 1) : d378786 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376497, d378786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39627 q selected
    | true =>
      simp only [d376497, d378786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39629 q selected
  have h2 (q : Pattern) (selected : d376499 q = 1) : d376499 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d376500 q = 1) : d378787 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376500, d378787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376500, d378787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d376501 q = 1) : d378788 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376501, d378788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376501, d378788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376502 q = 1) : d378789 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d376502, d378789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376502, d378789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376506 q = 1) : d378793 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376506, d378793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376506, d378793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39630 q selected
  have h8 (q : Pattern) (selected : d352297 q = 1) : d352297 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d376507 q = 1) : d378794 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376507, d378794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376507, d378794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376508 q = 1) : d378795 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376508, d378795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376508, d378795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d376509 q = 1) : d378796 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d376509, d378796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376509, d378796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d376510 q = 1) : d378797 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d376510, d378797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376510, d378797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d376565 q = 1) : d378803 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376565, d378803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376565, d378803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39634 q selected
  have h14 (q : Pattern) (selected : d352362 q = 1) : d352362 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d376566 q = 1) : d378804 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376566, d378804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376566, d378804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d376567 q = 1) : d378805 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376567, d378805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d376567, d378805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d376568 q = 1) : d378806 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d376568, d378806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d376568, d378806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d376569 q = 1) : d378807 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d376569, d378807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d376569, d378807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d376570 q = 1) : d378808 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d376570, d378808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376570, d378808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro39636 (p : Pattern) (selected : d376576 p = 1) : d378814 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376571 q = 1) : d378809 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d376571, d378809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376571, d378809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39635 q selected
  have h2 (q : Pattern) (selected : d376572 q = 1) : d378810 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d376572, d378810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376572, d378810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376573 q = 1) : d378811 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d376573, d378811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376573, d378811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376574 q = 1) : d378812 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d376574, d378812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376574, d378812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376575 q = 1) : d378813 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d376575, d378813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376575, d378813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376576 q = 1) : d378814 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d376576, d378814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376576, d378814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39637 (p : Pattern) (selected : d376675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d352041 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d352041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352042 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d352042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376438 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d376438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376675 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d376675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro39638 (p : Pattern) (selected : d376681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376676 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39637 q selected
    | true =>
      simp only [d376676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376677 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376440 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39622 q selected
    | true =>
      simp only [d376440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376441 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376678 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352045 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36990 q selected
    | true =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352046 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376442 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376679 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376680 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352047 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d376443 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d376444 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d376681 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d376681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro39639 (p : Pattern) (selected : d376689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376440 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39622 q selected
    | true =>
      simp only [d376440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376441 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352045 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36990 q selected
    | true =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352046 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376442 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376687 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376688 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352047 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352048 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d352049 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376689 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d376689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39640 (p : Pattern) (selected : d376695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376682 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39638 q selected
    | true =>
      simp only [d376682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376683 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376684 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376685 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376446 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39623 q selected
    | true =>
      simp only [d376446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376447 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376448 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376449 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376686 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376690 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39639 q selected
    | true =>
      simp only [d376690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376691 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d376692 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d376693 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d352051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36991 q selected
    | true =>
      simp only [d352051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d352052 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d352052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d352053 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d352054 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d352054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d376694 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d376695 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro39641 (p : Pattern) (selected : d376702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376696 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39640 q selected
    | true =>
      simp only [d376696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39624 q selected
  have h2 (q : Pattern) (selected : d376697 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376698 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376452 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39624 q selected
    | true =>
      simp only [d376452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36992 q selected
  have h5 (q : Pattern) (selected : d376453 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376454 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376699 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376700 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376701 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376702 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39642 (p : Pattern) (selected : d376706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376452 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39624 q selected
    | true =>
      simp only [d376452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36992 q selected
  have h2 (q : Pattern) (selected : d376453 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376454 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376700 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376705 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376706 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39643 (p : Pattern) (selected : d376712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376703 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39641 q selected
    | true =>
      simp only [d376703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376704 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376707 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39642 q selected
    | true =>
      simp only [d376707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376708 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376709 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376710 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376711 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376712 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39644 (p : Pattern) (selected : d376716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376707 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39642 q selected
    | true =>
      simp only [d376707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376708 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376713 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376714 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376715 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376716 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39645 (p : Pattern) (selected : d376728 p = 1) : d378820 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376621 q = 1) : d376621 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d376630 q = 1) : d376630 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d376674 q = 1) : d376674 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d376717 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39643 q selected
    | true =>
      simp only [d376717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39644 q selected
  have h5 (q : Pattern) (selected : d376718 q = 1) : d378816 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376718, d378816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376718, d378816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376724 q = 1) : d376724 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d376725 q = 1) : d378817 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376725, d378817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376725, d378817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376726 q = 1) : d378818 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376726, d378818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376726, d378818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376727 q = 1) : d378819 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376727, d378819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376727, d378819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376728 q = 1) : d378820 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376728, d378820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376728, d378820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro39646 (p : Pattern) (selected : d376742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376703 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39641 q selected
    | true =>
      simp only [d376703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376704 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376707 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39642 q selected
    | true =>
      simp only [d376707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376708 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376709 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376710 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376711 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376742 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39647 (p : Pattern) (selected : d376743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376707 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39642 q selected
    | true =>
      simp only [d376707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376708 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376713 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376714 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376715 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376743 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39648 (p : Pattern) (selected : d376752 p = 1) : d378825 p = 1 := by
  have h0 (q : Pattern) (selected : d376621 q = 1) : d376621 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376630 q = 1) : d376630 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d376674 q = 1) : d376674 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d376717 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39643 q selected
    | true =>
      simp only [d376717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39644 q selected
  have h4 (q : Pattern) (selected : d376718 q = 1) : d378816 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376718, d378816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376718, d378816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376724 q = 1) : d376724 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d376725 q = 1) : d378817 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376725, d378817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376725, d378817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376726 q = 1) : d378818 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376726, d378818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376726, d378818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376727 q = 1) : d378819 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376727, d378819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376727, d378819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376734 q = 1) : d376734 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d376739 q = 1) : d376739 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d376741 q = 1) : d376741 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d376744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39646 q selected
    | true =>
      simp only [d376744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39647 q selected
  have h13 (q : Pattern) (selected : d376745 q = 1) : d378821 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376745, d378821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d376745, d378821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d376748 q = 1) : d376748 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d376749 q = 1) : d378822 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376749, d378822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376749, d378822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d376750 q = 1) : d378823 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376750, d378823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376750, d378823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d376751 q = 1) : d378824 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376751, d378824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376751, d378824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d376752 q = 1) : d378825 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376752, d378825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376752, d378825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro39649 (p : Pattern) (selected : d376772 p = 1) : d378832 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376741 q = 1) : d376741 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d376744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39646 q selected
    | true =>
      simp only [d376744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39647 q selected
  have h3 (q : Pattern) (selected : d376745 q = 1) : d378821 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376745, d378821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376745, d378821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376748 q = 1) : d376748 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d376749 q = 1) : d378822 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376749, d378822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376749, d378822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376770 q = 1) : d378830 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376770, d378830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376770, d378830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376771 q = 1) : d378831 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376771, d378831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376771, d378831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376772 q = 1) : d378832 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376772, d378832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376772, d378832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39650 (p : Pattern) (selected : d376835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376825 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39638 q selected
  have h2 (q : Pattern) (selected : d376682 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39638 q selected
    | true =>
      simp only [d376682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376826 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376683 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376827 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376828 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376535 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39623 q selected
  have h8 (q : Pattern) (selected : d376446 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39623 q selected
    | true =>
      simp only [d376446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376536 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376447 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d376447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376537 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d376538 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d376538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d376829 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d376830 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39639 q selected
  have h15 (q : Pattern) (selected : d376690 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39639 q selected
    | true =>
      simp only [d376690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d376831 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d376831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d376691 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d376691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d376832 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d376832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d376833 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d376833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d352126 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36991 q selected
  have h21 (q : Pattern) (selected : d352051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36991 q selected
    | true =>
      simp only [d352051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d352127 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d352127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d352052 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d352052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d352128 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d352128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d352129 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d352129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d376834 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d376834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d376834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d376835 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d376835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro39651 (p : Pattern) (selected : d376842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376836 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39650 q selected
    | true =>
      simp only [d376836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39631 q selected
  have h2 (q : Pattern) (selected : d376837 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376838 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376541 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39631 q selected
    | true =>
      simp only [d376541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36999 q selected
  have h5 (q : Pattern) (selected : d376542 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376543 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376839 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376840 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d376841 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376842 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39652 (p : Pattern) (selected : d376846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376541 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d376541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39631 q selected
    | true =>
      simp only [d376541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36999 q selected
  have h2 (q : Pattern) (selected : d376542 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d376542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376543 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d376543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376840 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d376840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376845 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d376845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376846 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d376846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39653 (p : Pattern) (selected : d376852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376843 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39651 q selected
    | true =>
      simp only [d376843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376844 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376847 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39652 q selected
    | true =>
      simp only [d376847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376848 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376849 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376850 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376851 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376852 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39654 (p : Pattern) (selected : d376856 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376847 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d376847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39652 q selected
    | true =>
      simp only [d376847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376848 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d376848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376853 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d376853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376854 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d376854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376855 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d376855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376856 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39655 (p : Pattern) (selected : d376868 p = 1) : d378842 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376824 q = 1) : d376824 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d376857 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d376857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39653 q selected
    | true =>
      simp only [d376857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39654 q selected
  have h3 (q : Pattern) (selected : d376858 q = 1) : d378838 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d376858, d378838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376858, d378838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376864 q = 1) : d376864 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d376865 q = 1) : d378839 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d376865, d378839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376865, d378839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376866 q = 1) : d378840 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d376866, d378840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376866, d378840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376867 q = 1) : d378841 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d376867, d378841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376867, d378841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376868 q = 1) : d378842 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d376868, d378842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376868, d378842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39656 (p : Pattern) (selected : d376885 p = 1) : d378848 p = 1 := by
  have h0 (q : Pattern) (selected : d376613 q = 1) : d376613 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376753 q = 1) : d378826 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376753, d378826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39645 q selected
    | true =>
      simp only [d376753, d378826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39648 q selected
  have h2 (q : Pattern) (selected : d376766 q = 1) : d376766 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d376767 q = 1) : d378827 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376767, d378827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376767, d378827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d376768 q = 1) : d378828 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376768, d378828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376768, d378828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376769 q = 1) : d378829 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d376769, d378829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376769, d378829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376773 q = 1) : d378833 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376773, d378833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376773, d378833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39649 q selected
  have h8 (q : Pattern) (selected : d376775 q = 1) : d376775 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d376776 q = 1) : d378834 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376776, d378834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376776, d378834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376777 q = 1) : d378835 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376777, d378835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376777, d378835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d376778 q = 1) : d378836 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d376778, d378836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d376778, d378836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d376779 q = 1) : d378837 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d376779, d378837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376779, d378837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d376869 q = 1) : d378843 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d376869, d378843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376869, d378843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39655 q selected
  have h14 (q : Pattern) (selected : d376880 q = 1) : d376880 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d376881 q = 1) : d378844 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d376881, d378844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d376881, d378844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d376882 q = 1) : d378845 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d376882, d378845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d376882, d378845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d376883 q = 1) : d378846 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d376883, d378846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d376883, d378846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d376884 q = 1) : d378847 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d376884, d378847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d376884, d378847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d376885 q = 1) : d378848 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d376885, d378848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376885, d378848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro39657 (p : Pattern) (selected : d376891 p = 1) : d378854 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376886 q = 1) : d378849 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d376886, d378849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376886, d378849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39656 q selected
  have h2 (q : Pattern) (selected : d376887 q = 1) : d378850 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d376887, d378850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376887, d378850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d376888 q = 1) : d378851 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d376888, d378851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376888, d378851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376889 q = 1) : d378852 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d376889, d378852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376889, d378852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d376890 q = 1) : d378853 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d376890, d378853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376890, d378853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376891 q = 1) : d378854 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d376891, d378854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376891, d378854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39658 (p : Pattern) (selected : d377000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376676 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39637 q selected
    | true =>
      simp only [d376676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376677 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376997 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376440 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39622 q selected
    | true =>
      simp only [d376440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376441 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d376678 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d376998 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376999 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352045 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36990 q selected
    | true =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d352046 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d376442 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d376679 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d376679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d376680 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d376680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d377000 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d377000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro39659 (p : Pattern) (selected : d377008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376676 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39637 q selected
    | true =>
      simp only [d376676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376677 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376440 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39622 q selected
    | true =>
      simp only [d376440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d376441 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376678 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352045 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36990 q selected
    | true =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352046 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d376442 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d376442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d376679 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d376680 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d376680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d377005 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h12 (q : Pattern) (selected : d377006 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d377006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d377006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d377007 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d377007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d377007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d377008 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d377008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro39660 (p : Pattern) (selected : d377017 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376676 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39637 q selected
    | true =>
      simp only [d376676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376677 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377014 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377015 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d377015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377016 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d377016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352045 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36990 q selected
    | true =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352046 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377005 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d377006 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d377006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d377007 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d377007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d377017 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d377017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39661 (p : Pattern) (selected : d377022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376440 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d376440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39622 q selected
    | true =>
      simp only [d376440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376441 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d376441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352045 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36990 q selected
    | true =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352046 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376442 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d376442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352047 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d376443 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d376443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d376444 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d376444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d376444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377022 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d377022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro39662 (p : Pattern) (selected : d377028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377001 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39658 q selected
    | true =>
      simp only [d377001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377002 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377003 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377004 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377009 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39659 q selected
    | true =>
      simp only [d377009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377010 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377011 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377012 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377013 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377018 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39660 q selected
    | true =>
      simp only [d377018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d377019 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d377020 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d377021 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d377021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d377023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39661 q selected
    | true =>
      simp only [d377023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d377024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d377024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d377025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d377026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d377026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d377027 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d377028 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro39663 (p : Pattern) (selected : d377031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376682 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39638 q selected
    | true =>
      simp only [d376682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d376683 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376684 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376685 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39661 q selected
    | true =>
      simp only [d377023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377029 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377030 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d377031 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39664 (p : Pattern) (selected : d377035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39661 q selected
    | true =>
      simp only [d377023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377030 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377035 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39665 (p : Pattern) (selected : d377042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377032 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39662 q selected
    | true =>
      simp only [d377032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39663 q selected
  have h2 (q : Pattern) (selected : d377033 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377034 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377036 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39663 q selected
    | true =>
      simp only [d377036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39664 q selected
  have h5 (q : Pattern) (selected : d377037 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377038 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377039 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377040 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377041 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377042 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39666 (p : Pattern) (selected : d377046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377036 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39663 q selected
    | true =>
      simp only [d377036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39664 q selected
  have h2 (q : Pattern) (selected : d377037 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377038 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377040 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377045 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377046 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39667 (p : Pattern) (selected : d377052 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377043 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39665 q selected
    | true =>
      simp only [d377043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377044 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377047 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39666 q selected
    | true =>
      simp only [d377047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377048 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377049 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377050 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377051 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377052 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39668 (p : Pattern) (selected : d377056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377047 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39666 q selected
    | true =>
      simp only [d377047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377048 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377053 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377054 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377055 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377056 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39669 (p : Pattern) (selected : d377068 p = 1) : d378861 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376955 q = 1) : d376955 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d376964 q = 1) : d376964 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d376996 q = 1) : d376996 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d377057 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39667 q selected
    | true =>
      simp only [d377057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39668 q selected
  have h5 (q : Pattern) (selected : d377058 q = 1) : d378857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377058, d378857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377058, d378857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377064 q = 1) : d377064 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d377065 q = 1) : d378858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377065, d378858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377065, d378858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377066 q = 1) : d378859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377066, d378859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377066, d378859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d377067 q = 1) : d378860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377067, d378860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377067, d378860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377068 q = 1) : d378861 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377068, d378861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377068, d378861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro39670 (p : Pattern) (selected : d377082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377043 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39665 q selected
    | true =>
      simp only [d377043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377044 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377047 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39666 q selected
    | true =>
      simp only [d377047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377048 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377049 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377050 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377051 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377082 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39671 (p : Pattern) (selected : d377083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377047 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39666 q selected
    | true =>
      simp only [d377047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377048 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377053 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377054 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377055 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377083 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39672 (p : Pattern) (selected : d377092 p = 1) : d378866 p = 1 := by
  have h0 (q : Pattern) (selected : d376955 q = 1) : d376955 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376964 q = 1) : d376964 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d376996 q = 1) : d376996 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d377057 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39667 q selected
    | true =>
      simp only [d377057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39668 q selected
  have h4 (q : Pattern) (selected : d377058 q = 1) : d378857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377058, d378857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377058, d378857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377064 q = 1) : d377064 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d377065 q = 1) : d378858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377065, d378858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377065, d378858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377066 q = 1) : d378859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377066, d378859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377066, d378859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377067 q = 1) : d378860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377067, d378860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377067, d378860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d377074 q = 1) : d377074 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d377079 q = 1) : d377079 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d377081 q = 1) : d377081 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d377084 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39670 q selected
    | true =>
      simp only [d377084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39671 q selected
  have h13 (q : Pattern) (selected : d377085 q = 1) : d378862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377085, d378862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d377085, d378862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d377088 q = 1) : d377088 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d377089 q = 1) : d378863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377089, d378863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377089, d378863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d377090 q = 1) : d378864 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377090, d378864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377090, d378864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d377091 q = 1) : d378865 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377091, d378865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377091, d378865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d377092 q = 1) : d378866 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377092, d378866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377092, d378866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro39673 (p : Pattern) (selected : d377112 p = 1) : d378873 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377081 q = 1) : d377081 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d377084 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39670 q selected
    | true =>
      simp only [d377084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39671 q selected
  have h3 (q : Pattern) (selected : d377085 q = 1) : d378862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377085, d378862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377085, d378862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377088 q = 1) : d377088 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d377089 q = 1) : d378863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377089, d378863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377089, d378863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377110 q = 1) : d378871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377110, d378871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377110, d378871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377111 q = 1) : d378872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377111, d378872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377111, d378872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377112 q = 1) : d378873 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377112, d378873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377112, d378873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39674 (p : Pattern) (selected : d377196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39658 q selected
  have h2 (q : Pattern) (selected : d377001 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39658 q selected
    | true =>
      simp only [d377001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377002 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377182 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39659 q selected
  have h8 (q : Pattern) (selected : d377009 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39659 q selected
    | true =>
      simp only [d377009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377183 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377010 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d377184 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d377185 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d377185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d377186 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d377187 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39660 q selected
  have h15 (q : Pattern) (selected : d377018 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39660 q selected
    | true =>
      simp only [d377018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d377188 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d377188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d377019 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d377019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d377189 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d377189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d377190 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d377190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d377191 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39661 q selected
  have h21 (q : Pattern) (selected : d377023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39661 q selected
    | true =>
      simp only [d377023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d377192 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d377192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d377024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d377024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d377193 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d377193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d377194 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d377194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d377195 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d377195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d377196 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro39675 (p : Pattern) (selected : d377199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d376825 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39638 q selected
  have h2 (q : Pattern) (selected : d376682 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d376682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39638 q selected
    | true =>
      simp only [d376682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d376826 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d376683 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d376683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d376683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d376827 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d376827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d376827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d376828 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d376828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d376828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377191 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39661 q selected
  have h8 (q : Pattern) (selected : d377023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39661 q selected
    | true =>
      simp only [d377023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377192 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d377193 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d377194 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d377194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d377197 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d377198 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d377198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d377199 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro39676 (p : Pattern) (selected : d377203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377191 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39661 q selected
  have h2 (q : Pattern) (selected : d377023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39661 q selected
    | true =>
      simp only [d377023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377192 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377193 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377194 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377198 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377203 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39677 (p : Pattern) (selected : d377210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39674 q selected
    | true =>
      simp only [d377200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39675 q selected
  have h2 (q : Pattern) (selected : d377201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39675 q selected
    | true =>
      simp only [d377204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39676 q selected
  have h5 (q : Pattern) (selected : d377205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377207 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377208 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377209 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377210 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39678 (p : Pattern) (selected : d377214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39675 q selected
    | true =>
      simp only [d377204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39676 q selected
  have h2 (q : Pattern) (selected : d377205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377208 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377213 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377214 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39679 (p : Pattern) (selected : d377220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377211 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39677 q selected
    | true =>
      simp only [d377211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377212 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377215 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39678 q selected
    | true =>
      simp only [d377215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377216 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377217 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377218 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377219 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377220 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39680 (p : Pattern) (selected : d377224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377215 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39678 q selected
    | true =>
      simp only [d377215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377216 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377221 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377222 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377223 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377224 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39681 (p : Pattern) (selected : d377236 p = 1) : d378883 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377177 q = 1) : d377177 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d377225 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39679 q selected
    | true =>
      simp only [d377225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39680 q selected
  have h3 (q : Pattern) (selected : d377226 q = 1) : d378879 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377226, d378879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377226, d378879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377232 q = 1) : d377232 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d377233 q = 1) : d378880 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377233, d378880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377233, d378880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377234 q = 1) : d378881 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377234, d378881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377234, d378881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377235 q = 1) : d378882 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377235, d378882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377235, d378882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377236 q = 1) : d378883 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377236, d378883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377236, d378883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39682 (p : Pattern) (selected : d377253 p = 1) : d378889 p = 1 := by
  have h0 (q : Pattern) (selected : d376947 q = 1) : d376947 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377093 q = 1) : d378867 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377093, d378867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39669 q selected
    | true =>
      simp only [d377093, d378867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39672 q selected
  have h2 (q : Pattern) (selected : d377106 q = 1) : d377106 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d377107 q = 1) : d378868 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d377107, d378868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377107, d378868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d377108 q = 1) : d378869 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d377108, d378869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377108, d378869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377109 q = 1) : d378870 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d377109, d378870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377109, d378870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377113 q = 1) : d378874 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377113, d378874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377113, d378874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39673 q selected
  have h8 (q : Pattern) (selected : d377115 q = 1) : d377115 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d377116 q = 1) : d378875 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d377116, d378875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377116, d378875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377117 q = 1) : d378876 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d377117, d378876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377117, d378876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d377118 q = 1) : d378877 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d377118, d378877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377118, d378877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d377119 q = 1) : d378878 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d377119, d378878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377119, d378878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d377237 q = 1) : d378884 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377237, d378884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377237, d378884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39681 q selected
  have h14 (q : Pattern) (selected : d377248 q = 1) : d377248 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d377249 q = 1) : d378885 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d377249, d378885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377249, d378885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d377250 q = 1) : d378886 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d377250, d378886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d377250, d378886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d377251 q = 1) : d378887 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d377251, d378887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d377251, d378887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d377252 q = 1) : d378888 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d377252, d378888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d377252, d378888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d377253 q = 1) : d378889 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d377253, d378889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d377253, d378889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro39683 (p : Pattern) (selected : d377259 p = 1) : d378895 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377254 q = 1) : d378890 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d377254, d378890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377254, d378890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39682 q selected
  have h2 (q : Pattern) (selected : d377255 q = 1) : d378891 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d377255, d378891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377255, d378891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377256 q = 1) : d378892 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d377256, d378892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377256, d378892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377257 q = 1) : d378893 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d377257, d378893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377257, d378893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377258 q = 1) : d378894 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d377258, d378894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377258, d378894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377259 q = 1) : d378895 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d377259, d378895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377259, d378895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39684 (p : Pattern) (selected : d377365 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d353344 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d353344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d353344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36990 q selected
  have h2 (q : Pattern) (selected : d377359 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d377359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377360 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352045 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36990 q selected
    | true =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377361 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d377361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377362 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377363 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d377363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377364 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d377364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377365 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d377365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro39685 (p : Pattern) (selected : d377371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377366 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39684 q selected
    | true =>
      simp only [d377366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377368 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377369 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377370 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377371 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39686 (p : Pattern) (selected : d377373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377366 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39684 q selected
    | true =>
      simp only [d377366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377368 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377369 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377370 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377372 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377373 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro39687 (p : Pattern) (selected : d377377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d353344 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d353344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d353344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36990 q selected
  have h2 (q : Pattern) (selected : d377359 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d377359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377360 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352045 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36990 q selected
    | true =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377361 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d377361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377362 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377363 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d377363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377364 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d377364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377377 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d377377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro39688 (p : Pattern) (selected : d377383 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377366 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39684 q selected
    | true =>
      simp only [d377366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377368 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377369 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377372 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377378 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39687 q selected
    | true =>
      simp only [d377378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377379 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377380 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d377381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d377382 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d377383 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro39689 (p : Pattern) (selected : d377390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377374 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39685 q selected
    | true =>
      simp only [d377374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39686 q selected
  have h2 (q : Pattern) (selected : d377375 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377376 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377384 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39686 q selected
    | true =>
      simp only [d377384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39688 q selected
  have h5 (q : Pattern) (selected : d377385 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377386 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377387 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377388 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377390 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39690 (p : Pattern) (selected : d377394 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377384 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39686 q selected
    | true =>
      simp only [d377384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39688 q selected
  have h2 (q : Pattern) (selected : d377385 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377386 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377388 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377393 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377394 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39691 (p : Pattern) (selected : d377400 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377391 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39689 q selected
    | true =>
      simp only [d377391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377392 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377395 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39690 q selected
    | true =>
      simp only [d377395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377396 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377397 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377398 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377399 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377400 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39692 (p : Pattern) (selected : d377404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377395 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39690 q selected
    | true =>
      simp only [d377395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377396 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377401 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377402 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377403 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377404 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39693 (p : Pattern) (selected : d377425 p = 1) : d378904 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377336 q = 1) : d377336 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d377345 q = 1) : d377345 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d377358 q = 1) : d377358 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d377405 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39691 q selected
    | true =>
      simp only [d377405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39692 q selected
  have h5 (q : Pattern) (selected : d377406 q = 1) : d378900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377406, d378900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377406, d378900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377421 q = 1) : d377421 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d377422 q = 1) : d378901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377422, d378901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377422, d378901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377423 q = 1) : d378902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377423, d378902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377423, d378902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d377424 q = 1) : d378903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377424, d378903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377424, d378903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377425 q = 1) : d378904 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377425, d378904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377425, d378904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro39694 (p : Pattern) (selected : d377439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377391 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39689 q selected
    | true =>
      simp only [d377391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377392 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377395 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39690 q selected
    | true =>
      simp only [d377395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377396 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377397 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377398 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377399 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377439 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39695 (p : Pattern) (selected : d377440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377395 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39690 q selected
    | true =>
      simp only [d377395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377396 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377401 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377402 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377403 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377440 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39696 (p : Pattern) (selected : d377449 p = 1) : d378909 p = 1 := by
  have h0 (q : Pattern) (selected : d377336 q = 1) : d377336 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377345 q = 1) : d377345 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d377358 q = 1) : d377358 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d377405 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39691 q selected
    | true =>
      simp only [d377405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39692 q selected
  have h4 (q : Pattern) (selected : d377406 q = 1) : d378900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377406, d378900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377406, d378900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377421 q = 1) : d377421 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d377422 q = 1) : d378901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377422, d378901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377422, d378901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377423 q = 1) : d378902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377423, d378902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377423, d378902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377424 q = 1) : d378903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377424, d378903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377424, d378903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d377431 q = 1) : d377431 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d377436 q = 1) : d377436 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d377438 q = 1) : d377438 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d377441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39694 q selected
    | true =>
      simp only [d377441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39695 q selected
  have h13 (q : Pattern) (selected : d377442 q = 1) : d378905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377442, d378905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d377442, d378905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d377445 q = 1) : d377445 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d377446 q = 1) : d378906 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377446, d378906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377446, d378906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d377447 q = 1) : d378907 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377447, d378907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377447, d378907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d377448 q = 1) : d378908 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377448, d378908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377448, d378908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d377449 q = 1) : d378909 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377449, d378909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377449, d378909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro39697 (p : Pattern) (selected : d377469 p = 1) : d378916 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377438 q = 1) : d377438 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d377441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39694 q selected
    | true =>
      simp only [d377441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39695 q selected
  have h3 (q : Pattern) (selected : d377442 q = 1) : d378905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377442, d378905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377442, d378905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377445 q = 1) : d377445 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d377446 q = 1) : d378906 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377446, d378906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377446, d378906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377467 q = 1) : d378914 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377467, d378914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377467, d378914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377468 q = 1) : d378915 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377468, d378915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377468, d378915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377469 q = 1) : d378916 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377469, d378916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377469, d378916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39698 (p : Pattern) (selected : d377529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377524 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39684 q selected
  have h2 (q : Pattern) (selected : d377366 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39684 q selected
    | true =>
      simp only [d377366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377525 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377526 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377527 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377528 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377529 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39699 (p : Pattern) (selected : d377531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377524 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39684 q selected
  have h2 (q : Pattern) (selected : d377366 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39684 q selected
    | true =>
      simp only [d377366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377525 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377526 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377527 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377528 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377530 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377531 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro39700 (p : Pattern) (selected : d377540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377524 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39684 q selected
  have h2 (q : Pattern) (selected : d377366 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39684 q selected
    | true =>
      simp only [d377366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377525 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377526 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377527 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377530 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377535 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39687 q selected
  have h9 (q : Pattern) (selected : d377378 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39687 q selected
    | true =>
      simp only [d377378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d377536 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377379 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d377537 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d377538 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d377538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d377539 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d377540 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro39701 (p : Pattern) (selected : d377547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39698 q selected
    | true =>
      simp only [d377532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39699 q selected
  have h2 (q : Pattern) (selected : d377533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377541 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39699 q selected
    | true =>
      simp only [d377541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39700 q selected
  have h5 (q : Pattern) (selected : d377542 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377543 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377544 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377545 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377546 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377547 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39702 (p : Pattern) (selected : d377551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377541 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39699 q selected
    | true =>
      simp only [d377541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39700 q selected
  have h2 (q : Pattern) (selected : d377542 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377543 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377545 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377550 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377551 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39703 (p : Pattern) (selected : d377557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377548 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39701 q selected
    | true =>
      simp only [d377548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377549 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377552 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39702 q selected
    | true =>
      simp only [d377552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377553 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377554 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377555 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377556 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377557 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro39704 (p : Pattern) (selected : d377563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377558 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d377558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39622 q selected
    | true =>
      simp only [d377558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36990 q selected
  have h2 (q : Pattern) (selected : d377559 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d377559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377560 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352045 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36990 q selected
    | true =>
      simp only [d352045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377361 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d377361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377362 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d377362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377561 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d377561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377562 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d377562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d377563 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d377563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro39705 (p : Pattern) (selected : d377569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377524 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39684 q selected
  have h2 (q : Pattern) (selected : d377366 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39684 q selected
    | true =>
      simp only [d377366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377525 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377526 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377527 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d377530 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d377535 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39687 q selected
  have h9 (q : Pattern) (selected : d377378 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39687 q selected
    | true =>
      simp only [d377378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d377536 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d377536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377564 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d377564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39704 q selected
    | true =>
      simp only [d377564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d377565 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d377565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d377565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d377566 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d377566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d377567 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d377567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d377568 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d377568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d377568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d377569 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d377569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro39706 (p : Pattern) (selected : d377575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377570 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d377570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39699 q selected
    | true =>
      simp only [d377570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39705 q selected
  have h2 (q : Pattern) (selected : d377571 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d377571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377572 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d377572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377573 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d377573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377574 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d377574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377575 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d377575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39707 (p : Pattern) (selected : d377581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377576 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d377576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39706 q selected
    | true =>
      simp only [d377576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377577 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d377577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377578 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d377578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377579 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d377579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d377580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377581 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d377581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39708 (p : Pattern) (selected : d377602 p = 1) : d378926 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377523 q = 1) : d377523 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d377582 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39703 q selected
    | true =>
      simp only [d377582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39707 q selected
  have h3 (q : Pattern) (selected : d377583 q = 1) : d378922 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d377583, d378922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377583, d378922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377598 q = 1) : d377598 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d377599 q = 1) : d378923 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d377599, d378923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377599, d378923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377600 q = 1) : d378924 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d377600, d378924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377600, d378924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377601 q = 1) : d378925 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d377601, d378925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377601, d378925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d377602 q = 1) : d378926 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d377602, d378926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377602, d378926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro39709 (p : Pattern) (selected : d377619 p = 1) : d378932 p = 1 := by
  have h0 (q : Pattern) (selected : d377328 q = 1) : d377328 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377450 q = 1) : d378910 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377450, d378910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39693 q selected
    | true =>
      simp only [d377450, d378910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39696 q selected
  have h2 (q : Pattern) (selected : d377463 q = 1) : d377463 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d377464 q = 1) : d378911 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d377464, d378911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377464, d378911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d377465 q = 1) : d378912 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d377465, d378912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377465, d378912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377466 q = 1) : d378913 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d377466, d378913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377466, d378913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377470 q = 1) : d378917 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377470, d378917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377470, d378917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39697 q selected
  have h8 (q : Pattern) (selected : d377472 q = 1) : d377472 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d377473 q = 1) : d378918 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d377473, d378918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377473, d378918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377474 q = 1) : d378919 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d377474, d378919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d377474, d378919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d377475 q = 1) : d378920 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d377475, d378920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d377475, d378920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d377476 q = 1) : d378921 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d377476, d378921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377476, d378921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d377603 q = 1) : d378927 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d377603, d378927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377603, d378927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39708 q selected
  have h14 (q : Pattern) (selected : d377614 q = 1) : d377614 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d377615 q = 1) : d378928 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d377615, d378928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d377615, d378928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d377616 q = 1) : d378929 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d377616, d378929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d377616, d378929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d377617 q = 1) : d378930 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d377617, d378930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d377617, d378930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d377618 q = 1) : d378931 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d377618, d378931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d377618, d378931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d377619 q = 1) : d378932 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d377619, d378932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d377619, d378932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro39710 (p : Pattern) (selected : d377625 p = 1) : d378938 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377620 q = 1) : d378933 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d377620, d378933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377620, d378933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39709 q selected
  have h2 (q : Pattern) (selected : d377621 q = 1) : d378934 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d377621, d378934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377621, d378934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d377622 q = 1) : d378935 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d377622, d378935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377622, d378935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377623 q = 1) : d378936 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d377623, d378936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377623, d378936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d377624 q = 1) : d378937 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d377624, d378937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377624, d378937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377625 q = 1) : d378938 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d377625, d378938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d377625, d378938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39711 (p : Pattern) (selected : d377631 p = 1) : d378944 p = 1 := by
  have h0 (q : Pattern) (selected : d376577 q = 1) : d378815 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d376577, d378815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39621 q selected
    | true =>
      simp only [d376577, d378815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39636 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d376892 q = 1) : d378855 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d376892, d378855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d376892, d378855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39657 q selected
  have h3 (q : Pattern) (selected : d376893 q = 1) : d378856 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d376893, d378856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d376893, d378856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d377260 q = 1) : d378896 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d377260, d378896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377260, d378896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39683 q selected
  have h5 (q : Pattern) (selected : d377261 q = 1) : d378897 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d377261, d378897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377261, d378897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d377262 q = 1) : d378898 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d377262, d378898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377262, d378898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d377263 q = 1) : d378899 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d377263, d378899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d377263, d378899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d377626 q = 1) : d378939 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d377626, d378939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377626, d378939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39710 q selected
  have h9 (q : Pattern) (selected : d377627 q = 1) : d378940 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d377627, d378940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377627, d378940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d377628 q = 1) : d378941 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d377628, d378941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377628, d378941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377629 q = 1) : d378942 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d377629, d378942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377629, d378942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d377630 q = 1) : d378943 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d377630, d378943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d377630, d378943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d377631 q = 1) : d378944 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d377631, d378944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d377631, d378944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h13 p selected
theorem eqIntro39712 (p : Pattern) (selected : d377637 p = 1) : d378950 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377632 q = 1) : d378945 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d377632, d378945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39711 q selected
    | true =>
      simp only [d377632, d378945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377633 q = 1) : d378946 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d377633, d378946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377633, d378946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377634 q = 1) : d378947 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d377634, d378947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377634, d378947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377635 q = 1) : d378948 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d377635, d378948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377635, d378948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377636 q = 1) : d378949 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d377636, d378949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377636, d378949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377637 q = 1) : d378950 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d377637, d378950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377637, d378950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39713 (p : Pattern) (selected : d377643 p = 1) : d378956 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377638 q = 1) : d378951 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d377638, d378951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39712 q selected
    | true =>
      simp only [d377638, d378951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377639 q = 1) : d378952 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d377639, d378952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377639, d378952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377640 q = 1) : d378953 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d377640, d378953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377640, d378953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377641 q = 1) : d378954 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d377641, d378954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377641, d378954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377642 q = 1) : d378955 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d377642, d378955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377642, d378955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377643 q = 1) : d378956 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d377643, d378956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377643, d378956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39714 (p : Pattern) (selected : d377649 p = 1) : d378962 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377644 q = 1) : d378957 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d377644, d378957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39713 q selected
    | true =>
      simp only [d377644, d378957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377645 q = 1) : d378958 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d377645, d378958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377645, d378958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377646 q = 1) : d378959 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d377646, d378959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377646, d378959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377647 q = 1) : d378960 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d377647, d378960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377647, d378960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377648 q = 1) : d378961 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d377648, d378961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377648, d378961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377649 q = 1) : d378962 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d377649, d378962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377649, d378962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39715 (p : Pattern) (selected : d377655 p = 1) : d378968 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377650 q = 1) : d378963 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d377650, d378963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39714 q selected
    | true =>
      simp only [d377650, d378963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377651 q = 1) : d378964 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d377651, d378964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377651, d378964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377652 q = 1) : d378965 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d377652, d378965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377652, d378965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377653 q = 1) : d378966 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d377653, d378966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377653, d378966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377654 q = 1) : d378967 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d377654, d378967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377654, d378967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377655 q = 1) : d378968 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d377655, d378968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377655, d378968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39716 (p : Pattern) (selected : d377661 p = 1) : d378974 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377656 q = 1) : d378969 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d377656, d378969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39715 q selected
    | true =>
      simp only [d377656, d378969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377657 q = 1) : d378970 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d377657, d378970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377657, d378970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377658 q = 1) : d378971 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d377658, d378971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377658, d378971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377659 q = 1) : d378972 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d377659, d378972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377659, d378972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377660 q = 1) : d378973 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d377660, d378973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377660, d378973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377661 q = 1) : d378974 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d377661, d378974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377661, d378974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39717 (p : Pattern) (selected : d377667 p = 1) : d378980 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377662 q = 1) : d378975 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d377662, d378975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39716 q selected
    | true =>
      simp only [d377662, d378975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377663 q = 1) : d378976 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d377663, d378976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377663, d378976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377664 q = 1) : d378977 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d377664, d378977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377664, d378977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377665 q = 1) : d378978 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d377665, d378978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377665, d378978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377666 q = 1) : d378979 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d377666, d378979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377666, d378979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377667 q = 1) : d378980 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d377667, d378980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377667, d378980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39718 (p : Pattern) (selected : d377673 p = 1) : d378986 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d377668 q = 1) : d378981 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d377668, d378981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39717 q selected
    | true =>
      simp only [d377668, d378981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d377669 q = 1) : d378982 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d377669, d378982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d377669, d378982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d377670 q = 1) : d378983 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d377670, d378983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d377670, d378983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d377671 q = 1) : d378984 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d377671, d378984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d377671, d378984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d377672 q = 1) : d378985 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d377672, d378985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d377672, d378985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377673 q = 1) : d378986 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d377673, d378986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d377673, d378986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39719 (p : Pattern) (selected : d47329 p = 0) : d378994 p = 1 := by
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
  have h7 (q : Pattern) (selected : d47327 q = 0) : d378992 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47327, d378992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47327, d378992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d47328 q = 0) : d378993 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47328, d378993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47328, d378993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d47329 q = 0) : d378994 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47329, d378994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d47329, d378994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h9 p selected
theorem eqIntro39720 (p : Pattern) (selected : d47335 p = 0) : d379000 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47330 q = 0) : d378995 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47330, d378995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39719 q selected
    | true =>
      simp only [d47330, d378995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47331 q = 0) : d378996 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47331, d378996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47331, d378996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47332 q = 0) : d378997 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47332, d378997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47332, d378997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47333 q = 0) : d378998 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47333, d378998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47333, d378998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47334 q = 0) : d378999 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47334, d378999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47334, d378999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47335 q = 0) : d379000 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47335, d379000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47335, d379000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39721 (p : Pattern) (selected : d47341 p = 0) : d379006 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47336 q = 0) : d379001 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47336, d379001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39720 q selected
    | true =>
      simp only [d47336, d379001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47337 q = 0) : d379002 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47337, d379002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47337, d379002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47338 q = 0) : d379003 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47338, d379003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47338, d379003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47339 q = 0) : d379004 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47339, d379004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47339, d379004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47340 q = 0) : d379005 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47340, d379005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47340, d379005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47341 q = 0) : d379006 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47341, d379006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47341, d379006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39722 (p : Pattern) (selected : d47347 p = 0) : d379012 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47342 q = 0) : d379007 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47342, d379007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39721 q selected
    | true =>
      simp only [d47342, d379007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47343 q = 0) : d379008 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47343, d379008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47343, d379008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47344 q = 0) : d379009 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47344, d379009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47344, d379009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47345 q = 0) : d379010 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47345, d379010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47345, d379010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47346 q = 0) : d379011 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47346, d379011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47346, d379011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47347 q = 0) : d379012 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47347, d379012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47347, d379012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39723 (p : Pattern) (selected : d47353 p = 0) : d379018 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47348 q = 0) : d379013 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47348, d379013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39722 q selected
    | true =>
      simp only [d47348, d379013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47349 q = 0) : d379014 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47349, d379014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47349, d379014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47350 q = 0) : d379015 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47350, d379015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47350, d379015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47351 q = 0) : d379016 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47351, d379016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47351, d379016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47352 q = 0) : d379017 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47352, d379017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47352, d379017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47353 q = 0) : d379018 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47353, d379018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47353, d379018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39724 (p : Pattern) (selected : d47359 p = 0) : d379024 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47354 q = 0) : d379019 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47354, d379019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39723 q selected
    | true =>
      simp only [d47354, d379019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47355 q = 0) : d379020 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47355, d379020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47355, d379020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47356 q = 0) : d379021 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47356, d379021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47356, d379021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47357 q = 0) : d379022 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47357, d379022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47357, d379022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47358 q = 0) : d379023 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47358, d379023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47358, d379023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47359 q = 0) : d379024 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47359, d379024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47359, d379024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39725 (p : Pattern) (selected : d47365 p = 0) : d379030 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47360 q = 0) : d379025 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47360, d379025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39724 q selected
    | true =>
      simp only [d47360, d379025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47361 q = 0) : d379026 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47361, d379026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47361, d379026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47362 q = 0) : d379027 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47362, d379027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47362, d379027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47363 q = 0) : d379028 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47363, d379028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47363, d379028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47364 q = 0) : d379029 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47364, d379029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47364, d379029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47365 q = 0) : d379030 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47365, d379030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47365, d379030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39726 (p : Pattern) (selected : d47371 p = 0) : d379036 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47366 q = 0) : d379031 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47366, d379031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39725 q selected
    | true =>
      simp only [d47366, d379031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47367 q = 0) : d379032 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47367, d379032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47367, d379032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47368 q = 0) : d379033 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47368, d379033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47368, d379033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47369 q = 0) : d379034 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47369, d379034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47369, d379034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47370 q = 0) : d379035 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47370, d379035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47370, d379035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47371 q = 0) : d379036 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47371, d379036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47371, d379036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39727 (p : Pattern) (selected : d47284 p = 2) : d375686 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 2) : d367652 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d367652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38288 q selected
    | true =>
      simp only [d45496, d367652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38350 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d45903 q = 2) : d367679 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45903, d367679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45903, d367679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38427 q selected
  have h3 (q : Pattern) (selected : d45904 q = 2) : d367680 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d45904, d367680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45904, d367680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46456 q = 2) : d367707 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d46456, d367707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46456, d367707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38515 q selected
  have h5 (q : Pattern) (selected : d46457 q = 2) : d367708 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d46457, d367708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46457, d367708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46458 q = 2) : d367709 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d46458, d367709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46458, d367709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46860 q = 2) : d321904 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d46860, d321904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46860, d321904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38594 q selected
  have h8 (q : Pattern) (selected : d46861 q = 2) : d321905 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d46861, d321905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46861, d321905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46862 q = 2) : d321906 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d46862, d321906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46862, d321906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46863 q = 2) : d367710 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d46863, d367710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46863, d367710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47283 q = 2) : d375685 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47283, d375685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47283, d375685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d47284 q = 2) : d375686 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47284, d375686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d47284, d375686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h12 p selected
theorem eqIntro39728 (p : Pattern) (selected : d47290 p = 2) : d375692 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47285 q = 2) : d375687 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47285, d375687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39727 q selected
    | true =>
      simp only [d47285, d375687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47286 q = 2) : d375688 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47286, d375688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47286, d375688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47287 q = 2) : d375689 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47287, d375689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47287, d375689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47288 q = 2) : d375690 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47288, d375690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47288, d375690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47289 q = 2) : d375691 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47289, d375691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47289, d375691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47290 q = 2) : d375692 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47290, d375692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47290, d375692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39729 (p : Pattern) (selected : d47296 p = 2) : d375698 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47291 q = 2) : d375693 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47291, d375693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39728 q selected
    | true =>
      simp only [d47291, d375693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47292 q = 2) : d375694 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47292, d375694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47292, d375694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47293 q = 2) : d375695 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47293, d375695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47293, d375695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47294 q = 2) : d375696 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47294, d375696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47294, d375696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47295 q = 2) : d375697 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47295, d375697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47295, d375697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47296 q = 2) : d375698 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47296, d375698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47296, d375698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39730 (p : Pattern) (selected : d47302 p = 2) : d375704 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47297 q = 2) : d375699 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47297, d375699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39729 q selected
    | true =>
      simp only [d47297, d375699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47298 q = 2) : d375700 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47298, d375700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47298, d375700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47299 q = 2) : d375701 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47299, d375701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47299, d375701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47300 q = 2) : d375702 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47300, d375702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47300, d375702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47301 q = 2) : d375703 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47301, d375703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47301, d375703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47302 q = 2) : d375704 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47302, d375704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47302, d375704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39731 (p : Pattern) (selected : d47308 p = 2) : d375710 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47303 q = 2) : d375705 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47303, d375705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39730 q selected
    | true =>
      simp only [d47303, d375705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47304 q = 2) : d375706 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47304, d375706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47304, d375706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47305 q = 2) : d375707 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47305, d375707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47305, d375707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47306 q = 2) : d375708 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47306, d375708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47306, d375708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47307 q = 2) : d375709 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47307, d375709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47307, d375709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47308 q = 2) : d375710 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47308, d375710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47308, d375710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39732 (p : Pattern) (selected : d47314 p = 2) : d375716 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47309 q = 2) : d375711 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47309, d375711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39731 q selected
    | true =>
      simp only [d47309, d375711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47310 q = 2) : d375712 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47310, d375712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47310, d375712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47311 q = 2) : d375713 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47311, d375713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47311, d375713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47312 q = 2) : d375714 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47312, d375714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47312, d375714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47313 q = 2) : d375715 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47313, d375715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47313, d375715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47314 q = 2) : d375716 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47314, d375716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47314, d375716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39733 (p : Pattern) (selected : d47320 p = 2) : d375722 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47315 q = 2) : d375717 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47315, d375717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39732 q selected
    | true =>
      simp only [d47315, d375717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47316 q = 2) : d375718 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47316, d375718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47316, d375718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47317 q = 2) : d375719 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47317, d375719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47317, d375719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47318 q = 2) : d375720 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47318, d375720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47318, d375720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47319 q = 2) : d375721 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47319, d375721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47319, d375721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47320 q = 2) : d375722 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47320, d375722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47320, d375722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39734 (p : Pattern) (selected : d47326 p = 2) : d375728 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47321 q = 2) : d375723 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47321, d375723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39733 q selected
    | true =>
      simp only [d47321, d375723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47322 q = 2) : d375724 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47322, d375724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47322, d375724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47323 q = 2) : d375725 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47323, d375725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47323, d375725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47324 q = 2) : d375726 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47324, d375726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47324, d375726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47325 q = 2) : d375727 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47325, d375727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47325, d375727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47326 q = 2) : d375728 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47326, d375728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47326, d375728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39735 (p : Pattern) (selected : d47329 p = 1) : d379039 p = 1 := by
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
  have h7 (q : Pattern) (selected : d47327 q = 1) : d379037 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47327, d379037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47327, d379037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d47328 q = 1) : d379038 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47328, d379038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47328, d379038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d47329 q = 1) : d379039 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47329, d379039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d47329, d379039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h9 p selected
theorem eqIntro39736 (p : Pattern) (selected : d47335 p = 1) : d379045 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47330 q = 1) : d379040 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47330, d379040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39735 q selected
    | true =>
      simp only [d47330, d379040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47331 q = 1) : d379041 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47331, d379041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47331, d379041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47332 q = 1) : d379042 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47332, d379042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47332, d379042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47333 q = 1) : d379043 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47333, d379043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47333, d379043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47334 q = 1) : d379044 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47334, d379044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47334, d379044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47335 q = 1) : d379045 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47335, d379045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47335, d379045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39737 (p : Pattern) (selected : d47341 p = 1) : d379051 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47336 q = 1) : d379046 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47336, d379046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39736 q selected
    | true =>
      simp only [d47336, d379046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47337 q = 1) : d379047 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47337, d379047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47337, d379047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47338 q = 1) : d379048 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47338, d379048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47338, d379048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47339 q = 1) : d379049 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47339, d379049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47339, d379049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47340 q = 1) : d379050 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47340, d379050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47340, d379050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47341 q = 1) : d379051 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47341, d379051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47341, d379051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39738 (p : Pattern) (selected : d47347 p = 1) : d379057 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47342 q = 1) : d379052 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47342, d379052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39737 q selected
    | true =>
      simp only [d47342, d379052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47343 q = 1) : d379053 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47343, d379053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47343, d379053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47344 q = 1) : d379054 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47344, d379054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47344, d379054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47345 q = 1) : d379055 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47345, d379055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47345, d379055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47346 q = 1) : d379056 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47346, d379056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47346, d379056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47347 q = 1) : d379057 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47347, d379057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47347, d379057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39739 (p : Pattern) (selected : d47353 p = 1) : d379063 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47348 q = 1) : d379058 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47348, d379058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39738 q selected
    | true =>
      simp only [d47348, d379058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47349 q = 1) : d379059 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47349, d379059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47349, d379059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47350 q = 1) : d379060 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47350, d379060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47350, d379060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47351 q = 1) : d379061 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47351, d379061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47351, d379061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47352 q = 1) : d379062 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47352, d379062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47352, d379062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47353 q = 1) : d379063 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47353, d379063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47353, d379063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39740 (p : Pattern) (selected : d47359 p = 1) : d379069 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47354 q = 1) : d379064 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47354, d379064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39739 q selected
    | true =>
      simp only [d47354, d379064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47355 q = 1) : d379065 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47355, d379065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47355, d379065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47356 q = 1) : d379066 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47356, d379066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47356, d379066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47357 q = 1) : d379067 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47357, d379067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47357, d379067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47358 q = 1) : d379068 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47358, d379068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47358, d379068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47359 q = 1) : d379069 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47359, d379069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47359, d379069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39741 (p : Pattern) (selected : d47365 p = 1) : d379075 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47360 q = 1) : d379070 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47360, d379070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39740 q selected
    | true =>
      simp only [d47360, d379070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47361 q = 1) : d379071 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47361, d379071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47361, d379071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47362 q = 1) : d379072 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47362, d379072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47362, d379072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47363 q = 1) : d379073 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47363, d379073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47363, d379073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47364 q = 1) : d379074 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47364, d379074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47364, d379074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47365 q = 1) : d379075 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47365, d379075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47365, d379075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39742 (p : Pattern) (selected : d47371 p = 1) : d379081 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47366 q = 1) : d379076 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47366, d379076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39741 q selected
    | true =>
      simp only [d47366, d379076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47367 q = 1) : d379077 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47367, d379077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47367, d379077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47368 q = 1) : d379078 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47368, d379078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47368, d379078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47369 q = 1) : d379079 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47369, d379079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47369, d379079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47370 q = 1) : d379080 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47370, d379080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47370, d379080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47371 q = 1) : d379081 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47371, d379081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47371, d379081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39743 (p : Pattern) (selected : d379138 p = 0) : d379182 p = 1 := by
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
  have h4 (q : Pattern) (selected : d379136 q = 0) : d379180 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379136, d379180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379136, d379180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d379137 q = 0) : d379181 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379137, d379181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379137, d379181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d379138 q = 0) : d379182 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379138, d379182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379138, d379182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro39744 (p : Pattern) (selected : d379144 p = 0) : d379188 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379139 q = 0) : d379183 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379139, d379183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39743 q selected
    | true =>
      simp only [d379139, d379183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379140 q = 0) : d379184 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379140, d379184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379140, d379184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379141 q = 0) : d379185 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379141, d379185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379141, d379185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379142 q = 0) : d379186 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379142, d379186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379142, d379186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379143 q = 0) : d379187 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379143, d379187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379143, d379187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379144 q = 0) : d379188 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379144, d379188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379144, d379188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39745 (p : Pattern) (selected : d379149 p = 0) : d379193 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379145 q = 0) : d379189 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379145, d379189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39744 q selected
    | true =>
      simp only [d379145, d379189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379146 q = 0) : d379190 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379146, d379190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379146, d379190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379147 q = 0) : d379191 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379147, d379191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379147, d379191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379148 q = 0) : d379192 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379148, d379192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379148, d379192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379149 q = 0) : d379193 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379149, d379193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379149, d379193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39746 (p : Pattern) (selected : d379155 p = 0) : d379199 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379150 q = 0) : d379194 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379150, d379194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39745 q selected
    | true =>
      simp only [d379150, d379194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379151 q = 0) : d379195 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379151, d379195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379151, d379195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379152 q = 0) : d379196 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379152, d379196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379152, d379196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379153 q = 0) : d379197 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379153, d379197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379153, d379197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379154 q = 0) : d379198 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379154, d379198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379154, d379198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379155 q = 0) : d379199 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379155, d379199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379155, d379199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39747 (p : Pattern) (selected : d379161 p = 0) : d379205 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379156 q = 0) : d379200 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379156, d379200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39746 q selected
    | true =>
      simp only [d379156, d379200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379157 q = 0) : d379201 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379157, d379201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379157, d379201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379158 q = 0) : d379202 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379158, d379202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379158, d379202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379159 q = 0) : d379203 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379159, d379203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379159, d379203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379160 q = 0) : d379204 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379160, d379204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379160, d379204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379161 q = 0) : d379205 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379161, d379205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379161, d379205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39748 (p : Pattern) (selected : d379167 p = 0) : d379211 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379162 q = 0) : d379206 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379162, d379206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39747 q selected
    | true =>
      simp only [d379162, d379206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379163 q = 0) : d379207 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379163, d379207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379163, d379207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379164 q = 0) : d379208 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379164, d379208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379164, d379208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379165 q = 0) : d379209 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379165, d379209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379165, d379209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379166 q = 0) : d379210 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379166, d379210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379166, d379210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379167 q = 0) : d379211 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379167, d379211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379167, d379211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39749 (p : Pattern) (selected : d379173 p = 0) : d379217 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379168 q = 0) : d379212 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379168, d379212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39748 q selected
    | true =>
      simp only [d379168, d379212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379169 q = 0) : d379213 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379169, d379213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379169, d379213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379170 q = 0) : d379214 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379170, d379214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379170, d379214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379171 q = 0) : d379215 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379171, d379215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379171, d379215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379172 q = 0) : d379216 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379172, d379216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379172, d379216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379173 q = 0) : d379217 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379173, d379217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379173, d379217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
