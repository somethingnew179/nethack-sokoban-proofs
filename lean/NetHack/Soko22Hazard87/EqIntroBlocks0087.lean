import NetHack.Soko22Hazard87.EqIntroBlocks0086
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro21750 (p : Pattern) (selected : d218277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218245 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d218245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21742 q selected
    | true =>
      simp only [d218245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21745 q selected
  have h2 (q : Pattern) (selected : d218246 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d218246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218247 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d218247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218259 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d218259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21745 q selected
    | true =>
      simp only [d218259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21747 q selected
  have h5 (q : Pattern) (selected : d218260 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d218260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218261 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d218261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d218262 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d218262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d218272 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d218272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21745 q selected
    | true =>
      simp only [d218272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21749 q selected
  have h9 (q : Pattern) (selected : d218273 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d218273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218274 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d218274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d218275 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d218275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d218275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d218276 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d218276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d218277 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d218277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d218277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro21751 (p : Pattern) (selected : d218281 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218272 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d218272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21745 q selected
    | true =>
      simp only [d218272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21749 q selected
  have h2 (q : Pattern) (selected : d218273 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d218273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218274 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d218274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218275 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d218275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218280 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d218280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218281 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d218281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21752 (p : Pattern) (selected : d218287 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218278 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d218278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21750 q selected
    | true =>
      simp only [d218278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d218279 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d218279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218282 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d218282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21751 q selected
    | true =>
      simp only [d218282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d218283 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d218283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d218284 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d218284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218285 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d218285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218286 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d218286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218287 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d218287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21753 (p : Pattern) (selected : d218291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218282 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d218282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21751 q selected
    | true =>
      simp only [d218282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d218283 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d218283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218288 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d218288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d218289 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d218289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218290 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d218290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218291 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d218291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21754 (p : Pattern) (selected : d218312 p = 1) : d222153 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218112 q = 1) : d218112 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d218121 q = 1) : d218121 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d218172 q = 1) : d218172 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d218292 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d218292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21752 q selected
    | true =>
      simp only [d218292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21753 q selected
  have h5 (q : Pattern) (selected : d218293 q = 1) : d222149 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d218293, d222149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218293, d222149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218308 q = 1) : d218308 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d218309 q = 1) : d222150 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d218309, d222150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218309, d222150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d218310 q = 1) : d222151 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d218310, d222151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218310, d222151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d218311 q = 1) : d222152 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d218311, d222152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218311, d222152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218312 q = 1) : d222153 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d218312, d222153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218312, d222153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro21755 (p : Pattern) (selected : d218327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218278 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d218278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21750 q selected
    | true =>
      simp only [d218278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d218279 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d218279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218282 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d218282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21751 q selected
    | true =>
      simp only [d218282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d218283 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d218283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d218284 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d218284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218285 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d218285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218286 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d218286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218327 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d218327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21756 (p : Pattern) (selected : d218328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218282 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d218282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21751 q selected
    | true =>
      simp only [d218282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d218283 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d218283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218288 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d218288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d218289 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d218289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218290 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d218290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218328 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d218328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21757 (p : Pattern) (selected : d218337 p = 1) : d222158 p = 1 := by
  have h0 (q : Pattern) (selected : d218112 q = 1) : d218112 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218121 q = 1) : d218121 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d218172 q = 1) : d218172 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d218292 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d218292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21752 q selected
    | true =>
      simp only [d218292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21753 q selected
  have h4 (q : Pattern) (selected : d218293 q = 1) : d222149 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d218293, d222149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218293, d222149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d218308 q = 1) : d218308 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d218309 q = 1) : d222150 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d218309, d222150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218309, d222150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d218310 q = 1) : d222151 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d218310, d222151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218310, d222151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d218311 q = 1) : d222152 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d218311, d222152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218311, d222152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d218318 q = 1) : d218318 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d218323 q = 1) : d218323 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d218326 q = 1) : d218326 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d218329 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d218329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21755 q selected
    | true =>
      simp only [d218329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21756 q selected
  have h13 (q : Pattern) (selected : d218330 q = 1) : d222154 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d218330, d222154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d218330, d222154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d218333 q = 1) : d218333 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d218334 q = 1) : d222155 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d218334, d222155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d218334, d222155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d218335 q = 1) : d222156 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d218335, d222156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d218335, d222156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d218336 q = 1) : d222157 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d218336, d222157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218336, d222157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d218337 q = 1) : d222158 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d218337, d222158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218337, d222158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro21758 (p : Pattern) (selected : d218362 p = 1) : d222165 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218326 q = 1) : d218326 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d218329 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d218329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21755 q selected
    | true =>
      simp only [d218329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21756 q selected
  have h3 (q : Pattern) (selected : d218330 q = 1) : d222154 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d218330, d222154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218330, d222154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218333 q = 1) : d218333 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d218334 q = 1) : d222155 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d218334, d222155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218334, d222155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218360 q = 1) : d222163 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d218360, d222163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218360, d222163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d218361 q = 1) : d222164 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d218361, d222164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218361, d222164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d218362 q = 1) : d222165 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d218362, d222165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218362, d222165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21759 (p : Pattern) (selected : d218486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218468 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21738 q selected
  have h2 (q : Pattern) (selected : d218199 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21738 q selected
    | true =>
      simp only [d218199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d218469 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218200 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218470 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218472 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21739 q selected
  have h8 (q : Pattern) (selected : d218204 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21739 q selected
    | true =>
      simp only [d218204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d218473 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218205 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d218474 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d218475 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d218475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d218476 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d218477 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21740 q selected
  have h15 (q : Pattern) (selected : d218213 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21740 q selected
    | true =>
      simp only [d218213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d218478 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d218478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d218214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d218214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d218479 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d218479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d218480 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d218480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d218481 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21741 q selected
  have h21 (q : Pattern) (selected : d218222 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21741 q selected
    | true =>
      simp only [d218222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d218482 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d218482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d218223 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d218223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d218483 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d218483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d218484 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d218484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d218485 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d218485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d218486 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d218486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d218486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro21760 (p : Pattern) (selected : d218497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218487 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21743 q selected
  have h2 (q : Pattern) (selected : d218233 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21743 q selected
    | true =>
      simp only [d218233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d218488 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218234 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218489 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218490 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218491 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21744 q selected
  have h8 (q : Pattern) (selected : d218238 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21744 q selected
    | true =>
      simp only [d218238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d218492 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218239 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d218493 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d218494 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d218494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d218495 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d218481 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21741 q selected
  have h15 (q : Pattern) (selected : d218222 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21741 q selected
    | true =>
      simp only [d218222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d218482 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d218482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d218223 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d218223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d218483 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d218483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d218484 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d218484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d218496 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d218496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d218497 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d218497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d218497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro21761 (p : Pattern) (selected : d218506 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218481 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21741 q selected
  have h2 (q : Pattern) (selected : d218222 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21741 q selected
    | true =>
      simp only [d218222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d218482 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218223 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218483 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218484 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218496 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218501 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21746 q selected
  have h9 (q : Pattern) (selected : d218253 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21746 q selected
    | true =>
      simp only [d218253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d218502 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d218254 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d218503 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d218503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d218504 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d218504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d218505 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d218505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d218506 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d218506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21762 (p : Pattern) (selected : d218516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21748 q selected
  have h2 (q : Pattern) (selected : d218266 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21748 q selected
    | true =>
      simp only [d218266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d218512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218267 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218515 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218501 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21746 q selected
  have h9 (q : Pattern) (selected : d218253 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21746 q selected
    | true =>
      simp only [d218253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d218502 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d218254 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d218503 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d218503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d218504 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d218504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d218505 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d218505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d218516 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d218516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21763 (p : Pattern) (selected : d218522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218498 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d218498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21759 q selected
    | true =>
      simp only [d218498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21760 q selected
  have h2 (q : Pattern) (selected : d218499 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d218499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218500 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d218500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218507 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d218507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21760 q selected
    | true =>
      simp only [d218507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21761 q selected
  have h5 (q : Pattern) (selected : d218508 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d218508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218509 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d218509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d218510 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d218510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d218517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d218517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21760 q selected
    | true =>
      simp only [d218517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21762 q selected
  have h9 (q : Pattern) (selected : d218518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d218518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d218519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d218520 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d218520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d218520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d218521 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d218521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d218522 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d218522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d218522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro21764 (p : Pattern) (selected : d218526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d218517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21760 q selected
    | true =>
      simp only [d218517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21762 q selected
  have h2 (q : Pattern) (selected : d218518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d218518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d218519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218520 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d218520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218525 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d218525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218526 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d218526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21765 (p : Pattern) (selected : d218532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218523 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d218523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21763 q selected
    | true =>
      simp only [d218523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d218524 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d218524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218527 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d218527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21764 q selected
    | true =>
      simp only [d218527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d218528 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d218528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d218529 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d218529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218530 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d218530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218531 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d218531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218532 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d218532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21766 (p : Pattern) (selected : d218536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218527 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d218527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21764 q selected
    | true =>
      simp only [d218527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d218528 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d218528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d218533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d218534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d218534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218535 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d218535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218536 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d218536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21767 (p : Pattern) (selected : d218557 p = 1) : d222175 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218467 q = 1) : d218467 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d218537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d218537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21765 q selected
    | true =>
      simp only [d218537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21766 q selected
  have h3 (q : Pattern) (selected : d218538 q = 1) : d222171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d218538, d222171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218538, d222171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218553 q = 1) : d218553 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d218554 q = 1) : d222172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d218554, d222172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218554, d222172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218555 q = 1) : d222173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d218555, d222173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218555, d222173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d218556 q = 1) : d222174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d218556, d222174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218556, d222174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d218557 q = 1) : d222175 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d218557, d222175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218557, d222175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21768 (p : Pattern) (selected : d218574 p = 1) : d222181 p = 1 := by
  have h0 (q : Pattern) (selected : d218104 q = 1) : d218104 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218338 q = 1) : d222159 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d218338, d222159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21754 q selected
    | true =>
      simp only [d218338, d222159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21757 q selected
  have h2 (q : Pattern) (selected : d218356 q = 1) : d218356 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d218357 q = 1) : d222160 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d218357, d222160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218357, d222160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d218358 q = 1) : d222161 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d218358, d222161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218358, d222161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218359 q = 1) : d222162 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d218359, d222162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218359, d222162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d218363 q = 1) : d222166 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d218363, d222166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218363, d222166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21758 q selected
  have h8 (q : Pattern) (selected : d218365 q = 1) : d218365 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d218366 q = 1) : d222167 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d218366, d222167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218366, d222167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218367 q = 1) : d222168 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d218367, d222168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218367, d222168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d218368 q = 1) : d222169 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d218368, d222169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d218368, d222169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d218369 q = 1) : d222170 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d218369, d222170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218369, d222170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d218558 q = 1) : d222176 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d218558, d222176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218558, d222176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21767 q selected
  have h14 (q : Pattern) (selected : d218569 q = 1) : d218569 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d218570 q = 1) : d222177 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d218570, d222177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d218570, d222177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d218571 q = 1) : d222178 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d218571, d222178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d218571, d222178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d218572 q = 1) : d222179 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d218572, d222179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d218572, d222179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d218573 q = 1) : d222180 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d218573, d222180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d218573, d222180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d218574 q = 1) : d222181 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d218574, d222181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d218574, d222181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro21769 (p : Pattern) (selected : d218580 p = 1) : d222187 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218575 q = 1) : d222182 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d218575, d222182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218575, d222182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21768 q selected
  have h2 (q : Pattern) (selected : d218576 q = 1) : d222183 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d218576, d222183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218576, d222183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218577 q = 1) : d222184 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d218577, d222184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218577, d222184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218578 q = 1) : d222185 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d218578, d222185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218578, d222185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d218579 q = 1) : d222186 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d218579, d222186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218579, d222186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218580 q = 1) : d222187 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d218580, d222187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218580, d222187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21770 (p : Pattern) (selected : d218774 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (selected : d562 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2163 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218773 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d218773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218774 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d218774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21771 (p : Pattern) (selected : d218776 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (selected : d563 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1691 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d218775 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d218775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218776 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d218776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21772 (p : Pattern) (selected : d218782 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (selected : d562 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2163 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218773 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d218773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218781 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d218781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218782 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d218782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro21773 (p : Pattern) (selected : d218784 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (selected : d563 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1691 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d218775 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d218775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d339 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2182 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d218783 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d218783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d218784 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d218784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro21774 (p : Pattern) (selected : d218789 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218777 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21770 q selected
    | true =>
      simp only [d218777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21771 q selected
  have h2 (q : Pattern) (selected : d218778 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218779 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d218779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d218780 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d218780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218785 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21772 q selected
    | true =>
      simp only [d218785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21773 q selected
  have h6 (q : Pattern) (selected : d218786 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d218787 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d218787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218788 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d218788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d218789 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d218789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21775 (p : Pattern) (selected : d218794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d218777 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21770 q selected
    | true =>
      simp only [d218777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21771 q selected
  have h1 (q : Pattern) (selected : d218785 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21772 q selected
    | true =>
      simp only [d218785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21773 q selected
  have h2 (q : Pattern) (selected : d218786 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d218787 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d218787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d218788 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d218788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h6 (q : Pattern) (selected : d218794 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d218794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h6 p selected
theorem eqIntro21776 (p : Pattern) (selected : d218803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d218777 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21770 q selected
    | true =>
      simp only [d218777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21771 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d218800 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218801 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d218801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d218802 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d218802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d218803 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d218803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro21777 (p : Pattern) (selected : d218811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d218785 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21772 q selected
    | true =>
      simp only [d218785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21773 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d218808 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218809 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d218809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d218810 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d218810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d218811 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d218811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro21778 (p : Pattern) (selected : d218817 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218790 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21774 q selected
    | true =>
      simp only [d218790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d218791 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d218792 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218793 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218795 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21775 q selected
    | true =>
      simp only [d218795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218796 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218797 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d218798 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d218799 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218804 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21776 q selected
    | true =>
      simp only [d218804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d218805 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d218805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d218806 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d218807 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d218807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d218812 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21777 q selected
    | true =>
      simp only [d218812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d218813 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d218813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d218814 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d218815 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d218815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d218816 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d218816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d218817 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d218817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro21779 (p : Pattern) (selected : d218818 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (selected : d562 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2163 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218781 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d218781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218818 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d218818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21780 (p : Pattern) (selected : d218819 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2182 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218783 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d218783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218819 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d218819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro21781 (p : Pattern) (selected : d218824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d218777 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21770 q selected
    | true =>
      simp only [d218777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21771 q selected
  have h1 (q : Pattern) (selected : d218785 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21772 q selected
    | true =>
      simp only [d218785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21773 q selected
  have h2 (q : Pattern) (selected : d218786 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d218787 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d218787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d218788 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d218788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h6 (q : Pattern) (selected : d218820 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21779 q selected
    | true =>
      simp only [d218820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21780 q selected
  have h7 (q : Pattern) (selected : d218821 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d218822 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d218822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h9 (q : Pattern) (selected : d218823 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d218823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h10 (q : Pattern) (selected : d218824 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d218824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro21782 (p : Pattern) (selected : d218829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d218785 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21772 q selected
    | true =>
      simp only [d218785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21773 q selected
  have h1 (q : Pattern) (selected : d218820 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21779 q selected
    | true =>
      simp only [d218820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21780 q selected
  have h2 (q : Pattern) (selected : d218821 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d218822 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d218822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d218823 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d218823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h6 (q : Pattern) (selected : d218829 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d218829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h6 p selected
theorem eqIntro21783 (p : Pattern) (selected : d218836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218825 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21781 q selected
    | true =>
      simp only [d218825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d218826 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d218827 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218828 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218830 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21782 q selected
    | true =>
      simp only [d218830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218831 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218832 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d218833 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d218834 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218812 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21777 q selected
    | true =>
      simp only [d218812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d218813 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d218813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d218814 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d218815 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d218815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d218835 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d218835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d218836 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d218836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21784 (p : Pattern) (selected : d218846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218840 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21780 q selected
  have h2 (q : Pattern) (selected : d218841 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d218842 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21780 q selected
    | true =>
      simp only [d218842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d218843 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218844 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d218844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218845 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d218845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218846 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d218846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro21785 (p : Pattern) (selected : d218852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218812 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21777 q selected
    | true =>
      simp only [d218812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d218813 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d218814 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218815 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218835 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218847 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21784 q selected
    | true =>
      simp only [d218847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218848 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218849 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d218850 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d218851 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d218852 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d218852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21786 (p : Pattern) (selected : d218859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d218785 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21772 q selected
    | true =>
      simp only [d218785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21773 q selected
  have h1 (q : Pattern) (selected : d218820 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21779 q selected
    | true =>
      simp only [d218820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21780 q selected
  have h2 (q : Pattern) (selected : d218821 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d218822 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d218822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d218823 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d218823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h6 (q : Pattern) (selected : d218840 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21780 q selected
  have h7 (q : Pattern) (selected : d218841 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h8 (q : Pattern) (selected : d218857 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d218857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h9 (q : Pattern) (selected : d218858 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d218858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h10 (q : Pattern) (selected : d218859 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d218859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro21787 (p : Pattern) (selected : d218865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218860 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21786 q selected
    | true =>
      simp only [d218860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d218861 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d218862 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218863 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218847 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21784 q selected
    | true =>
      simp only [d218847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218848 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218849 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d218850 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d218851 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d218865 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d218865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21788 (p : Pattern) (selected : d218871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218837 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d218837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21778 q selected
    | true =>
      simp only [d218837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21783 q selected
  have h2 (q : Pattern) (selected : d218838 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d218838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218839 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d218839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218853 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d218853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21783 q selected
    | true =>
      simp only [d218853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21785 q selected
  have h5 (q : Pattern) (selected : d218854 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d218854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218855 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d218855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d218856 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d218856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d218866 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d218866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21783 q selected
    | true =>
      simp only [d218866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21787 q selected
  have h9 (q : Pattern) (selected : d218867 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d218867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218868 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d218868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d218869 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d218869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d218869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d218870 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d218870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d218871 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d218871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d218871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro21789 (p : Pattern) (selected : d218875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218866 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d218866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21783 q selected
    | true =>
      simp only [d218866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21787 q selected
  have h2 (q : Pattern) (selected : d218867 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d218867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218868 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d218868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218869 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d218869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218874 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d218874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218875 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d218875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21790 (p : Pattern) (selected : d218881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d218872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21788 q selected
    | true =>
      simp only [d218872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d218873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d218873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218876 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d218876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21789 q selected
    | true =>
      simp only [d218876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d218877 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d218877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d218878 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d218878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218879 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d218879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218880 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d218880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218881 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d218881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21791 (p : Pattern) (selected : d218885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218876 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d218876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21789 q selected
    | true =>
      simp only [d218876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d218877 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d218877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218882 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d218882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d218883 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d218883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218884 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d218884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218885 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d218885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21792 (p : Pattern) (selected : d218906 p = 1) : d222196 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218724 q = 1) : d218724 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d218733 q = 1) : d218733 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d218772 q = 1) : d218772 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d218886 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d218886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21790 q selected
    | true =>
      simp only [d218886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21791 q selected
  have h5 (q : Pattern) (selected : d218887 q = 1) : d222192 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d218887, d222192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218887, d222192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218902 q = 1) : d218902 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d218903 q = 1) : d222193 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d218903, d222193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218903, d222193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d218904 q = 1) : d222194 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d218904, d222194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218904, d222194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d218905 q = 1) : d222195 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d218905, d222195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218905, d222195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218906 q = 1) : d222196 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d218906, d222196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218906, d222196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro21793 (p : Pattern) (selected : d218921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d218872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21788 q selected
    | true =>
      simp only [d218872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d218873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d218873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218876 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d218876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21789 q selected
    | true =>
      simp only [d218876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d218877 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d218877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d218878 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d218878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218879 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d218879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218880 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d218880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218921 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d218921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21794 (p : Pattern) (selected : d218922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218876 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d218876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21789 q selected
    | true =>
      simp only [d218876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d218877 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d218877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218882 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d218882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d218883 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d218883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218884 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d218884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218922 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d218922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21795 (p : Pattern) (selected : d218931 p = 1) : d222201 p = 1 := by
  have h0 (q : Pattern) (selected : d218724 q = 1) : d218724 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218733 q = 1) : d218733 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d218772 q = 1) : d218772 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d218886 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d218886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21790 q selected
    | true =>
      simp only [d218886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21791 q selected
  have h4 (q : Pattern) (selected : d218887 q = 1) : d222192 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d218887, d222192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218887, d222192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d218902 q = 1) : d218902 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d218903 q = 1) : d222193 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d218903, d222193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218903, d222193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d218904 q = 1) : d222194 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d218904, d222194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218904, d222194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d218905 q = 1) : d222195 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d218905, d222195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218905, d222195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d218912 q = 1) : d218912 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d218917 q = 1) : d218917 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d218920 q = 1) : d218920 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d218923 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d218923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21793 q selected
    | true =>
      simp only [d218923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21794 q selected
  have h13 (q : Pattern) (selected : d218924 q = 1) : d222197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d218924, d222197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d218924, d222197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d218927 q = 1) : d218927 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d218928 q = 1) : d222198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d218928, d222198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d218928, d222198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d218929 q = 1) : d222199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d218929, d222199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d218929, d222199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d218930 q = 1) : d222200 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d218930, d222200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218930, d222200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d218931 q = 1) : d222201 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d218931, d222201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218931, d222201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro21796 (p : Pattern) (selected : d218956 p = 1) : d222208 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218920 q = 1) : d218920 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d218923 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d218923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21793 q selected
    | true =>
      simp only [d218923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21794 q selected
  have h3 (q : Pattern) (selected : d218924 q = 1) : d222197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d218924, d222197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218924, d222197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218927 q = 1) : d218927 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d218928 q = 1) : d222198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d218928, d222198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218928, d222198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218954 q = 1) : d222206 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d218954, d222206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218954, d222206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d218955 q = 1) : d222207 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d218955, d222207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218955, d222207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d218956 q = 1) : d222208 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d218956, d222208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218956, d222208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21797 (p : Pattern) (selected : d219076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d219058 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d219058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21774 q selected
  have h2 (q : Pattern) (selected : d218790 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21774 q selected
    | true =>
      simp only [d218790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d219059 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d219059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d219059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218791 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d219060 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d219060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d219060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d219061 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d219061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d219061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d219062 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d219062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21775 q selected
  have h8 (q : Pattern) (selected : d218795 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21775 q selected
    | true =>
      simp only [d218795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d219063 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d219063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d219063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218796 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d219064 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d219064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d219064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d219065 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d219065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d219065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d219066 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d219066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d219066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d219067 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d219067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21776 q selected
  have h15 (q : Pattern) (selected : d218804 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21776 q selected
    | true =>
      simp only [d218804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d219068 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d219068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d219068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d218805 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d218805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d219069 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d219069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d219069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d219070 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d219070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d219070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d219071 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d219071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21777 q selected
  have h21 (q : Pattern) (selected : d218812 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21777 q selected
    | true =>
      simp only [d218812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d219072 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d219072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d219072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d218813 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d218813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d219073 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d219073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d219073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d219074 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d219074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d219074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d219075 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d219075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d219075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d219076 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d219076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d219076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro21798 (p : Pattern) (selected : d219087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d219077 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d219077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21781 q selected
  have h2 (q : Pattern) (selected : d218825 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21781 q selected
    | true =>
      simp only [d218825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d219078 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d219078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d219078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218826 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d219079 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d219079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d219079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d219080 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d219080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d219080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d219081 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d219081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21782 q selected
  have h8 (q : Pattern) (selected : d218830 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21782 q selected
    | true =>
      simp only [d218830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d219082 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d219082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d219082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218831 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d219083 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d219083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d219083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d219084 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d219084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d219084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d219085 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d219085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d219085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d219071 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d219071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21777 q selected
  have h15 (q : Pattern) (selected : d218812 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21777 q selected
    | true =>
      simp only [d218812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d219072 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d219072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d219072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d218813 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d218813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d219073 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d219073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d219073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d219074 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d219074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d219074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d219086 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d219086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d219086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d219087 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d219087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d219087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro21799 (p : Pattern) (selected : d219096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d219071 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d219071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21777 q selected
  have h2 (q : Pattern) (selected : d218812 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21777 q selected
    | true =>
      simp only [d218812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d219072 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d219072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d219072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218813 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d219073 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d219073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d219073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d219074 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d219074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d219074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d219086 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d219086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d219086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d219091 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d219091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21784 q selected
  have h9 (q : Pattern) (selected : d218847 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21784 q selected
    | true =>
      simp only [d218847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d219092 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d219092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d219092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d218848 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d219093 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d219093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d219093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d219094 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d219094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d219094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d219095 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d219095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d219095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d219096 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d219096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d219096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21800 (p : Pattern) (selected : d219106 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d219101 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d219101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21786 q selected
  have h2 (q : Pattern) (selected : d218860 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21786 q selected
    | true =>
      simp only [d218860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d219102 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d219102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d219102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d218861 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d218861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d219103 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d219103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d219103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d219104 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d219104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d219104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d219105 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d219105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d219105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d219091 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d219091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21784 q selected
  have h9 (q : Pattern) (selected : d218847 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21784 q selected
    | true =>
      simp only [d218847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d219092 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d219092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d219092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d218848 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d219093 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d219093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d219093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d219094 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d219094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d219094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d219095 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d219095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d219095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d219106 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d219106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d219106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21801 (p : Pattern) (selected : d219112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d219088 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d219088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21797 q selected
    | true =>
      simp only [d219088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21798 q selected
  have h2 (q : Pattern) (selected : d219089 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d219089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d219090 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d219090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d219097 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d219097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21798 q selected
    | true =>
      simp only [d219097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21799 q selected
  have h5 (q : Pattern) (selected : d219098 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d219098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d219099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d219099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d219100 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d219100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d219100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d219107 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d219107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21798 q selected
    | true =>
      simp only [d219107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21800 q selected
  have h9 (q : Pattern) (selected : d219108 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d219108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d219109 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d219109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d219110 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d219110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d219110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d219111 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d219111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d219111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d219112 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d219112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d219112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro21802 (p : Pattern) (selected : d219116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d219107 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d219107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21798 q selected
    | true =>
      simp only [d219107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21800 q selected
  have h2 (q : Pattern) (selected : d219108 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d219108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d219109 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d219109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d219110 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d219110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d219110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d219115 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d219115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d219115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d219116 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d219116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d219116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21803 (p : Pattern) (selected : d219122 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d219113 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d219113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21801 q selected
    | true =>
      simp only [d219113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d219114 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d219114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d219117 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d219117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21802 q selected
    | true =>
      simp only [d219117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d219118 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d219118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d219119 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d219119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d219119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d219120 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d219120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d219120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d219121 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d219121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d219121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d219122 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d219122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d219122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21804 (p : Pattern) (selected : d219126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d219117 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d219117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21802 q selected
    | true =>
      simp only [d219117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d219118 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d219118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d219123 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d219123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d219123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d219124 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d219124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d219124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d219125 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d219125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d219125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d219126 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d219126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d219126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21805 (p : Pattern) (selected : d219147 p = 1) : d222218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d219057 q = 1) : d219057 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d219127 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d219127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21803 q selected
    | true =>
      simp only [d219127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21804 q selected
  have h3 (q : Pattern) (selected : d219128 q = 1) : d222214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d219128, d222214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d219128, d222214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d219143 q = 1) : d219143 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d219144 q = 1) : d222215 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d219144, d222215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d219144, d222215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d219145 q = 1) : d222216 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d219145, d222216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219145, d222216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d219146 q = 1) : d222217 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d219146, d222217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219146, d222217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d219147 q = 1) : d222218 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d219147, d222218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219147, d222218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21806 (p : Pattern) (selected : d219164 p = 1) : d222224 p = 1 := by
  have h0 (q : Pattern) (selected : d218716 q = 1) : d218716 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d218932 q = 1) : d222202 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d218932, d222202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21792 q selected
    | true =>
      simp only [d218932, d222202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21795 q selected
  have h2 (q : Pattern) (selected : d218950 q = 1) : d218950 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d218951 q = 1) : d222203 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d218951, d222203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218951, d222203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d218952 q = 1) : d222204 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d218952, d222204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218952, d222204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d218953 q = 1) : d222205 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d218953, d222205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218953, d222205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d218957 q = 1) : d222209 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d218957, d222209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218957, d222209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21796 q selected
  have h8 (q : Pattern) (selected : d218959 q = 1) : d218959 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d218960 q = 1) : d222210 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d218960, d222210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218960, d222210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218961 q = 1) : d222211 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d218961, d222211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218961, d222211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d218962 q = 1) : d222212 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d218962, d222212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d218962, d222212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d218963 q = 1) : d222213 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d218963, d222213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218963, d222213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d219148 q = 1) : d222219 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d219148, d222219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d219148, d222219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21805 q selected
  have h14 (q : Pattern) (selected : d219159 q = 1) : d219159 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d219160 q = 1) : d222220 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d219160, d222220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d219160, d222220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d219161 q = 1) : d222221 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d219161, d222221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d219161, d222221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d219162 q = 1) : d222222 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d219162, d222222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d219162, d222222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d219163 q = 1) : d222223 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d219163, d222223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d219163, d222223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d219164 q = 1) : d222224 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d219164, d222224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d219164, d222224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro21807 (p : Pattern) (selected : d219170 p = 1) : d222230 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d219165 q = 1) : d222225 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d219165, d222225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219165, d222225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21806 q selected
  have h2 (q : Pattern) (selected : d219166 q = 1) : d222226 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d219166, d222226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219166, d222226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d219167 q = 1) : d222227 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d219167, d222227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219167, d222227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d219168 q = 1) : d222228 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d219168, d222228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219168, d222228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d219169 q = 1) : d222229 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d219169, d222229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219169, d222229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d219170 q = 1) : d222230 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d219170, d222230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219170, d222230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21808 (p : Pattern) (selected : d219176 p = 1) : d222236 p = 1 := by
  have h0 (q : Pattern) (selected : d217205 q = 1) : d222065 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d217205, d222065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21661 q selected
    | true =>
      simp only [d217205, d222065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21676 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d217538 q = 1) : d222105 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d217538, d222105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d217538, d222105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21699 q selected
  have h3 (q : Pattern) (selected : d217539 q = 1) : d222106 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d217539, d222106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d217539, d222106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d217968 q = 1) : d222146 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d217968, d222146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d217968, d222146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21729 q selected
  have h5 (q : Pattern) (selected : d217969 q = 1) : d222147 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d217969, d222147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d217969, d222147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d217970 q = 1) : d222148 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d217970, d222148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d217970, d222148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d218581 q = 1) : d222188 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d218581, d222188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218581, d222188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21769 q selected
  have h8 (q : Pattern) (selected : d218582 q = 1) : d222189 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d218582, d222189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218582, d222189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d218583 q = 1) : d222190 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d218583, d222190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d218583, d222190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218584 q = 1) : d222191 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d218584, d222191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218584, d222191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d219171 q = 1) : d222231 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d219171, d222231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d219171, d222231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21807 q selected
  have h12 (q : Pattern) (selected : d219172 q = 1) : d222232 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d219172, d222232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d219172, d222232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d219173 q = 1) : d222233 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d219173, d222233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d219173, d222233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d219174 q = 1) : d222234 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d219174, d222234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d219174, d222234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d219175 q = 1) : d222235 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d219175, d222235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d219175, d222235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d219176 q = 1) : d222236 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d219176, d222236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d219176, d222236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro21809 (p : Pattern) (selected : d219182 p = 1) : d222242 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d219177 q = 1) : d222237 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d219177, d222237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21808 q selected
    | true =>
      simp only [d219177, d222237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d219178 q = 1) : d222238 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d219178, d222238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d219178, d222238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d219179 q = 1) : d222239 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d219179, d222239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d219179, d222239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d219180 q = 1) : d222240 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d219180, d222240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d219180, d222240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d219181 q = 1) : d222241 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d219181, d222241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d219181, d222241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d219182 q = 1) : d222242 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d219182, d222242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d219182, d222242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21810 (p : Pattern) (selected : d219188 p = 1) : d222248 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d219183 q = 1) : d222243 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d219183, d222243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21809 q selected
    | true =>
      simp only [d219183, d222243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d219184 q = 1) : d222244 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d219184, d222244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d219184, d222244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d219185 q = 1) : d222245 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d219185, d222245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d219185, d222245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d219186 q = 1) : d222246 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d219186, d222246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d219186, d222246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d219187 q = 1) : d222247 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d219187, d222247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d219187, d222247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d219188 q = 1) : d222248 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d219188, d222248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d219188, d222248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21811 (p : Pattern) (selected : d219194 p = 1) : d222254 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d219189 q = 1) : d222249 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d219189, d222249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21810 q selected
    | true =>
      simp only [d219189, d222249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d219190 q = 1) : d222250 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d219190, d222250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d219190, d222250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d219191 q = 1) : d222251 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d219191, d222251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d219191, d222251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d219192 q = 1) : d222252 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d219192, d222252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d219192, d222252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d219193 q = 1) : d222253 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d219193, d222253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d219193, d222253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d219194 q = 1) : d222254 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d219194, d222254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d219194, d222254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21812 (p : Pattern) (selected : d219200 p = 1) : d222260 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d219195 q = 1) : d222255 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d219195, d222255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21811 q selected
    | true =>
      simp only [d219195, d222255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d219196 q = 1) : d222256 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d219196, d222256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d219196, d222256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d219197 q = 1) : d222257 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d219197, d222257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d219197, d222257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d219198 q = 1) : d222258 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d219198, d222258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d219198, d222258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d219199 q = 1) : d222259 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d219199, d222259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d219199, d222259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d219200 q = 1) : d222260 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d219200, d222260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d219200, d222260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21813 (p : Pattern) (selected : d219206 p = 1) : d222266 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d219201 q = 1) : d222261 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d219201, d222261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21812 q selected
    | true =>
      simp only [d219201, d222261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d219202 q = 1) : d222262 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d219202, d222262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d219202, d222262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d219203 q = 1) : d222263 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d219203, d222263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d219203, d222263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d219204 q = 1) : d222264 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d219204, d222264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d219204, d222264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d219205 q = 1) : d222265 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d219205, d222265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d219205, d222265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d219206 q = 1) : d222266 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d219206, d222266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d219206, d222266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21814 (p : Pattern) (selected : d219212 p = 1) : d222272 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d219207 q = 1) : d222267 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d219207, d222267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21813 q selected
    | true =>
      simp only [d219207, d222267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d219208 q = 1) : d222268 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d219208, d222268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d219208, d222268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d219209 q = 1) : d222269 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d219209, d222269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d219209, d222269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d219210 q = 1) : d222270 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d219210, d222270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d219210, d222270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d219211 q = 1) : d222271 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d219211, d222271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d219211, d222271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d219212 q = 1) : d222272 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d219212, d222272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d219212, d222272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21815 (p : Pattern) (selected : d219218 p = 1) : d222278 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d219213 q = 1) : d222273 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d219213, d222273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21814 q selected
    | true =>
      simp only [d219213, d222273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d219214 q = 1) : d222274 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d219214, d222274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d219214, d222274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d219215 q = 1) : d222275 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d219215, d222275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d219215, d222275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d219216 q = 1) : d222276 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d219216, d222276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d219216, d222276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d219217 q = 1) : d222277 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d219217, d222277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d219217, d222277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d219218 q = 1) : d222278 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d219218, d222278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d219218, d222278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21816 (p : Pattern) (selected : d222280 p = 0) : d223958 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116754 q = 0) : d118615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8830 q selected
    | true =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116755 q = 0) : d118616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116756 q = 0) : d118617 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116756, d118617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116756, d118617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116757 q = 0) : d118618 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116757, d118618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116757, d118618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116758 q = 0) : d118619 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116758, d118619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116758, d118619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222280 q = 0) : d223958 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222280, d223958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222280, d223958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21817 (p : Pattern) (selected : d222286 p = 0) : d223964 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222281 q = 0) : d223959 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222281, d223959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21816 q selected
    | true =>
      simp only [d222281, d223959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222282 q = 0) : d223960 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222282, d223960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222282, d223960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222283 q = 0) : d223961 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222283, d223961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222283, d223961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222284 q = 0) : d223962 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222284, d223962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222284, d223962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222285 q = 0) : d223963 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222285, d223963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222285, d223963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222286 q = 0) : d223964 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222286, d223964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222286, d223964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21818 (p : Pattern) (selected : d222292 p = 0) : d223970 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222287 q = 0) : d223965 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21817 q selected
    | true =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222288 q = 0) : d223966 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222289 q = 0) : d223967 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222289, d223967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222289, d223967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222290 q = 0) : d223968 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222290, d223968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222290, d223968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222291 q = 0) : d223969 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222291, d223969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222291, d223969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222292 q = 0) : d223970 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222292, d223970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222292, d223970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21819 (p : Pattern) (selected : d222298 p = 0) : d223976 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222293 q = 0) : d223971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222293, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21818 q selected
    | true =>
      simp only [d222293, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222294 q = 0) : d223972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222294, d223972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222294, d223972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d222295 q = 0) : d223973 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222295, d223973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222295, d223973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222296 q = 0) : d223974 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222296, d223974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222296, d223974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222297 q = 0) : d223975 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222297, d223975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222297, d223975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222298 q = 0) : d223976 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222298, d223976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222298, d223976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21820 (p : Pattern) (selected : d222299 p = 0) : d223977 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222287 q = 0) : d223965 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21817 q selected
    | true =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222288 q = 0) : d223966 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222289 q = 0) : d223967 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222289, d223967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222289, d223967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222290 q = 0) : d223968 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222290, d223968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222290, d223968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222291 q = 0) : d223969 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222291, d223969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222291, d223969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222299 q = 0) : d223977 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222299, d223977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222299, d223977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21821 (p : Pattern) (selected : d222305 p = 0) : d223983 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222293 q = 0) : d223971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222293, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21818 q selected
    | true =>
      simp only [d222293, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222294 q = 0) : d223972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222294, d223972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222294, d223972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d222295 q = 0) : d223973 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222295, d223973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222295, d223973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222296 q = 0) : d223974 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222296, d223974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222296, d223974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222297 q = 0) : d223975 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222297, d223975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222297, d223975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222300 q = 0) : d223978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222300, d223978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21820 q selected
    | true =>
      simp only [d222300, d223978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222301 q = 0) : d223979 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222301, d223979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222301, d223979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222302 q = 0) : d223980 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222302, d223980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222302, d223980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222303 q = 0) : d223981 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222303, d223981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222303, d223981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222304 q = 0) : d223982 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222304, d223982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222304, d223982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222305 q = 0) : d223983 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222305, d223983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222305, d223983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21822 (p : Pattern) (selected : d222310 p = 0) : d223988 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222300 q = 0) : d223978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222300, d223978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21820 q selected
    | true =>
      simp only [d222300, d223978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222301 q = 0) : d223979 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222301, d223979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222301, d223979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d222302 q = 0) : d223980 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222302, d223980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222302, d223980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222303 q = 0) : d223981 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222303, d223981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222303, d223981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222304 q = 0) : d223982 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222304, d223982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222304, d223982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222310 q = 0) : d223988 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222310, d223988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222310, d223988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21823 (p : Pattern) (selected : d222316 p = 0) : d223994 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116794 q = 0) : d118655 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116794, d118655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116794, d118655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8830 q selected
  have h2 (q : Pattern) (selected : d116754 q = 0) : d118615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8830 q selected
    | true =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116795 q = 0) : d118656 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116795, d118656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116795, d118656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116755 q = 0) : d118616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116796 q = 0) : d118657 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116796, d118657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116796, d118657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116797 q = 0) : d118658 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116797, d118658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116797, d118658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116798 q = 0) : d118659 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116798, d118659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116798, d118659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222316 q = 0) : d223994 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222316, d223994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222316, d223994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21824 (p : Pattern) (selected : d222322 p = 0) : d224000 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222317 q = 0) : d223995 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222317, d223995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21823 q selected
    | true =>
      simp only [d222317, d223995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222318 q = 0) : d223996 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222318, d223996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222318, d223996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222319 q = 0) : d223997 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222319, d223997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222319, d223997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222320 q = 0) : d223998 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222320, d223998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222320, d223998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222321 q = 0) : d223999 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222321, d223999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222321, d223999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222322 q = 0) : d224000 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222322, d224000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222322, d224000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21825 (p : Pattern) (selected : d222328 p = 0) : d224006 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222323 q = 0) : d224001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222323, d224001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21824 q selected
    | true =>
      simp only [d222323, d224001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222324 q = 0) : d224002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222324, d224002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222324, d224002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222325 q = 0) : d224003 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222325, d224003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222325, d224003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222326 q = 0) : d224004 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222326, d224004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222326, d224004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222327 q = 0) : d224005 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222327, d224005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222327, d224005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222328 q = 0) : d224006 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222328, d224006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222328, d224006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21826 (p : Pattern) (selected : d222334 p = 0) : d224012 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222329 q = 0) : d224007 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222329, d224007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21825 q selected
    | true =>
      simp only [d222329, d224007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222330 q = 0) : d224008 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222330, d224008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222330, d224008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d222331 q = 0) : d224009 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222331, d224009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222331, d224009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222332 q = 0) : d224010 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222332, d224010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222332, d224010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222333 q = 0) : d224011 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222333, d224011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222333, d224011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222334 q = 0) : d224012 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222334, d224012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222334, d224012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21827 (p : Pattern) (selected : d222340 p = 0) : d224018 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222306 q = 0) : d223984 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222306, d223984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21819 q selected
    | true =>
      simp only [d222306, d223984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21821 q selected
  have h2 (q : Pattern) (selected : d222307 q = 0) : d223985 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222307, d223985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222307, d223985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d222308 q = 0) : d223986 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222308, d223986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222308, d223986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222309 q = 0) : d223987 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222309, d223987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222309, d223987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222311 q = 0) : d223989 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222311, d223989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222311, d223989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21822 q selected
  have h6 (q : Pattern) (selected : d222312 q = 0) : d223990 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222312, d223990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222312, d223990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222313 q = 0) : d223991 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222313, d223991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222313, d223991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222314 q = 0) : d223992 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222314, d223992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222314, d223992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222315 q = 0) : d223993 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d222315, d223993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222315, d223993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222335 q = 0) : d224013 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222335, d224013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222335, d224013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21826 q selected
  have h11 (q : Pattern) (selected : d222336 q = 0) : d224014 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222336, d224014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222336, d224014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d222337 q = 0) : d224015 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222337, d224015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d222337, d224015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d222338 q = 0) : d224016 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222338, d224016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d222338, d224016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d222339 q = 0) : d224017 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d222339, d224017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d222339, d224017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d222340 q = 0) : d224018 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d222340, d224018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222340, d224018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21828 (p : Pattern) (selected : d222350 p = 0) : d224028 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222293 q = 0) : d223971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222293, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21818 q selected
    | true =>
      simp only [d222293, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222346 q = 0) : d224024 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222346, d224024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222346, d224024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222347 q = 0) : d224025 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222347, d224025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222347, d224025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222348 q = 0) : d224026 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222348, d224026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222348, d224026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222349 q = 0) : d224027 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222349, d224027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222349, d224027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222350 q = 0) : d224028 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222350, d224028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222350, d224028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21829 (p : Pattern) (selected : d222357 p = 0) : d224035 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222293 q = 0) : d223971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222293, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21818 q selected
    | true =>
      simp only [d222293, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222346 q = 0) : d224024 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222346, d224024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222346, d224024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222347 q = 0) : d224025 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222347, d224025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222347, d224025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222348 q = 0) : d224026 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222348, d224026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222348, d224026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222349 q = 0) : d224027 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222349, d224027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222349, d224027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222300 q = 0) : d223978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222300, d223978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21820 q selected
    | true =>
      simp only [d222300, d223978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222353 q = 0) : d224031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222353, d224031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222353, d224031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222354 q = 0) : d224032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222354, d224032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222354, d224032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222355 q = 0) : d224033 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222355, d224033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222355, d224033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222356 q = 0) : d224034 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222356, d224034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222356, d224034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222357 q = 0) : d224035 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222357, d224035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222357, d224035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21830 (p : Pattern) (selected : d222362 p = 0) : d224040 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222287 q = 0) : d223965 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21817 q selected
    | true =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222288 q = 0) : d223966 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222289 q = 0) : d223967 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222289, d223967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222289, d223967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222290 q = 0) : d223968 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222290, d223968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222290, d223968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222361 q = 0) : d224039 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222361, d224039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222361, d224039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222362 q = 0) : d224040 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222362, d224040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222362, d224040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21831 (p : Pattern) (selected : d222369 p = 0) : d224047 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222287 q = 0) : d223965 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21817 q selected
    | true =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222288 q = 0) : d223966 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222289 q = 0) : d223967 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222289, d223967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222289, d223967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222367 q = 0) : d224045 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222367, d224045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222367, d224045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222368 q = 0) : d224046 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222368, d224046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222368, d224046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222369 q = 0) : d224047 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222369, d224047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222369, d224047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21832 (p : Pattern) (selected : d222373 p = 0) : d224051 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116855 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8847 q selected
    | true =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116856 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116857 q = 0) : d118718 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116857, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116857, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116858 q = 0) : d118719 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116858, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116858, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116754 q = 0) : d118615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8830 q selected
    | true =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116755 q = 0) : d118616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116756 q = 0) : d118617 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116756, d118617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116756, d118617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116757 q = 0) : d118618 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116757, d118618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116757, d118618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d116859 q = 0) : d118720 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116859, d118720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116859, d118720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116758 q = 0) : d118619 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116758, d118619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d116758, d118619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d222373 q = 0) : d224051 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222373, d224051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222373, d224051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21833 (p : Pattern) (selected : d222379 p = 0) : d224057 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222374 q = 0) : d224052 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222374, d224052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21832 q selected
    | true =>
      simp only [d222374, d224052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21816 q selected
  have h2 (q : Pattern) (selected : d222375 q = 0) : d224053 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222375, d224053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222375, d224053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222376 q = 0) : d224054 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222376, d224054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222376, d224054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222281 q = 0) : d223959 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222281, d223959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21816 q selected
    | true =>
      simp only [d222281, d223959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222282 q = 0) : d223960 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222282, d223960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222282, d223960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222283 q = 0) : d223961 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222283, d223961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222283, d223961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222377 q = 0) : d224055 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222377, d224055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222377, d224055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222284 q = 0) : d223962 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222284, d223962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222284, d223962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222378 q = 0) : d224056 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222378, d224056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222378, d224056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222379 q = 0) : d224057 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222379, d224057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222379, d224057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21834 (p : Pattern) (selected : d222385 p = 0) : d224063 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222380 q = 0) : d224058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21833 q selected
    | true =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222381 q = 0) : d224059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222287 q = 0) : d223965 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21817 q selected
    | true =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222288 q = 0) : d223966 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222382 q = 0) : d224060 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222382, d224060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222382, d224060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222383 q = 0) : d224061 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222383, d224061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222383, d224061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222384 q = 0) : d224062 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222384, d224062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222384, d224062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222385 q = 0) : d224063 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222385, d224063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222385, d224063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21835 (p : Pattern) (selected : d222387 p = 0) : d223958 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116873 q = 0) : d118615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116873, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8851 q selected
    | true =>
      simp only [d116873, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116874 q = 0) : d118616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116874, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116874, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116875 q = 0) : d118617 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116875, d118617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116875, d118617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116876 q = 0) : d118618 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116876, d118618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116876, d118618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116877 q = 0) : d118619 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116877, d118619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116877, d118619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222387 q = 0) : d223958 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222387, d223958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222387, d223958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21836 (p : Pattern) (selected : d222393 p = 0) : d223964 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222388 q = 0) : d223959 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222388, d223959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21835 q selected
    | true =>
      simp only [d222388, d223959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222389 q = 0) : d223960 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222389, d223960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222389, d223960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222390 q = 0) : d223961 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222390, d223961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222390, d223961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222391 q = 0) : d223962 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222391, d223962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222391, d223962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222392 q = 0) : d223963 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222392, d223963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222392, d223963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222393 q = 0) : d223964 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222393, d223964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222393, d223964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21837 (p : Pattern) (selected : d222399 p = 0) : d223970 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222394 q = 0) : d223965 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222394, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21836 q selected
    | true =>
      simp only [d222394, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222395 q = 0) : d223966 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222395, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222395, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222396 q = 0) : d223967 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222396, d223967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222396, d223967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222397 q = 0) : d223968 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222397, d223968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222397, d223968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222398 q = 0) : d223969 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222398, d223969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222398, d223969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222399 q = 0) : d223970 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222399, d223970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222399, d223970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21838 (p : Pattern) (selected : d222405 p = 0) : d224069 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222363 q = 0) : d224041 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222363, d224041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21830 q selected
    | true =>
      simp only [d222363, d224041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222364 q = 0) : d224042 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222364, d224042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222364, d224042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222365 q = 0) : d224043 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222365, d224043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222365, d224043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222366 q = 0) : d224044 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222366, d224044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222366, d224044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222370 q = 0) : d224048 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222370, d224048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21831 q selected
    | true =>
      simp only [d222370, d224048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222371 q = 0) : d224049 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222371, d224049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222371, d224049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222372 q = 0) : d224050 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222372, d224050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222372, d224050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222386 q = 0) : d224064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222386, d224064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21834 q selected
    | true =>
      simp only [d222386, d224064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21818 q selected
  have h9 (q : Pattern) (selected : d222400 q = 0) : d223971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222400, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21837 q selected
    | true =>
      simp only [d222400, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d222401 q = 0) : d224065 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222401, d224065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222401, d224065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222293 q = 0) : d223971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222293, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21818 q selected
    | true =>
      simp only [d222293, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d222294 q = 0) : d223972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222294, d223972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d222294, d223972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d222402 q = 0) : d224066 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222402, d224066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222402, d224066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d222403 q = 0) : d224067 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222403, d224067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222403, d224067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d222404 q = 0) : d224068 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222404, d224068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222404, d224068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d222405 q = 0) : d224069 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222405, d224069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222405, d224069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro21839 (p : Pattern) (selected : d222406 p = 0) : d224070 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222287 q = 0) : d223965 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21817 q selected
    | true =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222288 q = 0) : d223966 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222289 q = 0) : d223967 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222289, d223967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222289, d223967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222290 q = 0) : d223968 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222290, d223968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222290, d223968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222361 q = 0) : d224039 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222361, d224039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222361, d224039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222406 q = 0) : d224070 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222406, d224070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222406, d224070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21840 (p : Pattern) (selected : d222411 p = 0) : d224075 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222287 q = 0) : d223965 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21817 q selected
    | true =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222288 q = 0) : d223966 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222289 q = 0) : d223967 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222289, d223967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222289, d223967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222367 q = 0) : d224045 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222367, d224045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222367, d224045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222368 q = 0) : d224046 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222368, d224046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222368, d224046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222411 q = 0) : d224075 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222411, d224075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222411, d224075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21841 (p : Pattern) (selected : d222415 p = 0) : d224079 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222380 q = 0) : d224058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21833 q selected
    | true =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222381 q = 0) : d224059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222287 q = 0) : d223965 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21817 q selected
    | true =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222288 q = 0) : d223966 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222382 q = 0) : d224060 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222382, d224060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222382, d224060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222383 q = 0) : d224061 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222383, d224061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222383, d224061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222384 q = 0) : d224062 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222384, d224062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222384, d224062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222415 q = 0) : d224079 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222415, d224079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222415, d224079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21842 (p : Pattern) (selected : d222417 p = 0) : d223977 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222394 q = 0) : d223965 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222394, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21836 q selected
    | true =>
      simp only [d222394, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222395 q = 0) : d223966 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222395, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222395, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222396 q = 0) : d223967 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222396, d223967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222396, d223967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222397 q = 0) : d223968 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222397, d223968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222397, d223968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222398 q = 0) : d223969 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222398, d223969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222398, d223969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222417 q = 0) : d223977 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222417, d223977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222417, d223977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21843 (p : Pattern) (selected : d222423 p = 0) : d224085 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222363 q = 0) : d224041 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222363, d224041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21830 q selected
    | true =>
      simp only [d222363, d224041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222364 q = 0) : d224042 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222364, d224042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222364, d224042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222365 q = 0) : d224043 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222365, d224043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222365, d224043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222366 q = 0) : d224044 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222366, d224044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222366, d224044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222370 q = 0) : d224048 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222370, d224048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21831 q selected
    | true =>
      simp only [d222370, d224048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222371 q = 0) : d224049 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222371, d224049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222371, d224049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222372 q = 0) : d224050 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222372, d224050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222372, d224050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222386 q = 0) : d224064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222386, d224064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21834 q selected
    | true =>
      simp only [d222386, d224064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21818 q selected
  have h9 (q : Pattern) (selected : d222400 q = 0) : d223971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222400, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21837 q selected
    | true =>
      simp only [d222400, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d222401 q = 0) : d224065 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222401, d224065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222401, d224065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222293 q = 0) : d223971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222293, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21818 q selected
    | true =>
      simp only [d222293, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d222294 q = 0) : d223972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222294, d223972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d222294, d223972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d222402 q = 0) : d224066 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222402, d224066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222402, d224066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d222403 q = 0) : d224067 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222403, d224067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222403, d224067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d222404 q = 0) : d224068 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222404, d224068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222404, d224068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d222407 q = 0) : d224071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222407, d224071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21839 q selected
    | true =>
      simp only [d222407, d224071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d222408 q = 0) : d224072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222408, d224072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222408, d224072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d222409 q = 0) : d224073 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222409, d224073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d222409, d224073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d222410 q = 0) : d224074 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222410, d224074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222410, d224074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d222412 q = 0) : d224076 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222412, d224076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21840 q selected
    | true =>
      simp only [d222412, d224076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d222413 q = 0) : d224077 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222413, d224077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222413, d224077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d222414 q = 0) : d224078 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222414, d224078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d222414, d224078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d222416 q = 0) : d224080 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222416, d224080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21841 q selected
    | true =>
      simp only [d222416, d224080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21820 q selected
  have h24 (q : Pattern) (selected : d222418 q = 0) : d223978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222418, d223978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21842 q selected
    | true =>
      simp only [d222418, d223978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d222419 q = 0) : d224081 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222419, d224081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d222419, d224081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d222300 q = 0) : d223978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222300, d223978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21820 q selected
    | true =>
      simp only [d222300, d223978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d222301 q = 0) : d223979 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222301, d223979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d222301, d223979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d222420 q = 0) : d224082 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222420, d224082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d222420, d224082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d222421 q = 0) : d224083 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222421, d224083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d222421, d224083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d222422 q = 0) : d224084 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222422, d224084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d222422, d224084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d222423 q = 0) : d224085 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222423, d224085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d222423, d224085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro21844 (p : Pattern) (selected : d222425 p = 0) : d224087 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222293 q = 0) : d223971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222293, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21818 q selected
    | true =>
      simp only [d222293, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222346 q = 0) : d224024 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222346, d224024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222346, d224024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222347 q = 0) : d224025 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222347, d224025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222347, d224025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222348 q = 0) : d224026 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222348, d224026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222348, d224026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222349 q = 0) : d224027 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222349, d224027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222349, d224027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222425 q = 0) : d224087 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222425, d224087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222425, d224087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21845 (p : Pattern) (selected : d222432 p = 0) : d224094 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222416 q = 0) : d224080 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222416, d224080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21841 q selected
    | true =>
      simp only [d222416, d224080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21820 q selected
  have h2 (q : Pattern) (selected : d222418 q = 0) : d223978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222418, d223978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21842 q selected
    | true =>
      simp only [d222418, d223978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d222419 q = 0) : d224081 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222419, d224081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222419, d224081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222300 q = 0) : d223978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222300, d223978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21820 q selected
    | true =>
      simp only [d222300, d223978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222301 q = 0) : d223979 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222301, d223979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222301, d223979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222420 q = 0) : d224082 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222420, d224082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222420, d224082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222430 q = 0) : d224092 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222430, d224092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222430, d224092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222431 q = 0) : d224093 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222431, d224093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222431, d224093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d222432 q = 0) : d224094 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222432, d224094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222432, d224094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21846 (p : Pattern) (selected : d222438 p = 0) : d224100 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116928 q = 0) : d118769 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116928, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116928, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8847 q selected
  have h2 (q : Pattern) (selected : d116855 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8847 q selected
    | true =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116929 q = 0) : d118770 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116929, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116929, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116856 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116930 q = 0) : d118771 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116930, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116930, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116931 q = 0) : d118772 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116931, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116931, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116794 q = 0) : d118655 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116794, d118655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116794, d118655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8830 q selected
  have h8 (q : Pattern) (selected : d116754 q = 0) : d118615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8830 q selected
    | true =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d116795 q = 0) : d118656 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116795, d118656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116795, d118656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116755 q = 0) : d118616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d116796 q = 0) : d118657 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116796, d118657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d116796, d118657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d116797 q = 0) : d118658 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116797, d118658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d116797, d118658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d116932 q = 0) : d118773 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116932, d118773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116932, d118773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d116798 q = 0) : d118659 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116798, d118659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d116798, d118659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d222438 q = 0) : d224100 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222438, d224100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d222438, d224100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21847 (p : Pattern) (selected : d222444 p = 0) : d224106 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222439 q = 0) : d224101 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222439, d224101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21846 q selected
    | true =>
      simp only [d222439, d224101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21823 q selected
  have h2 (q : Pattern) (selected : d222440 q = 0) : d224102 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222440, d224102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222440, d224102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222441 q = 0) : d224103 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222441, d224103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222441, d224103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222317 q = 0) : d223995 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222317, d223995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21823 q selected
    | true =>
      simp only [d222317, d223995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222318 q = 0) : d223996 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222318, d223996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222318, d223996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222319 q = 0) : d223997 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222319, d223997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222319, d223997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222442 q = 0) : d224104 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222442, d224104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222442, d224104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222320 q = 0) : d223998 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222320, d223998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222320, d223998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222443 q = 0) : d224105 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222443, d224105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222443, d224105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222444 q = 0) : d224106 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222444, d224106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222444, d224106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21848 (p : Pattern) (selected : d222450 p = 0) : d224112 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222445 q = 0) : d224107 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222445, d224107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21847 q selected
    | true =>
      simp only [d222445, d224107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222446 q = 0) : d224108 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222446, d224108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222446, d224108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222323 q = 0) : d224001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222323, d224001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21824 q selected
    | true =>
      simp only [d222323, d224001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222324 q = 0) : d224002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222324, d224002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222324, d224002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222447 q = 0) : d224109 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222447, d224109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222447, d224109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222448 q = 0) : d224110 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222448, d224110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222448, d224110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222449 q = 0) : d224111 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222449, d224111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222449, d224111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222450 q = 0) : d224112 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222450, d224112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222450, d224112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21849 (p : Pattern) (selected : d222452 p = 0) : d223994 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116946 q = 0) : d118655 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116946, d118655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116946, d118655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8851 q selected
  have h2 (q : Pattern) (selected : d116873 q = 0) : d118615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116873, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8851 q selected
    | true =>
      simp only [d116873, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116947 q = 0) : d118656 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116947, d118656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116947, d118656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116874 q = 0) : d118616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116874, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116874, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116948 q = 0) : d118657 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116948, d118657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116948, d118657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116949 q = 0) : d118658 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116949, d118658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116949, d118658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116950 q = 0) : d118659 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116950, d118659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116950, d118659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222452 q = 0) : d223994 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222452, d223994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222452, d223994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21850 (p : Pattern) (selected : d222458 p = 0) : d224000 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222453 q = 0) : d223995 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222453, d223995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21849 q selected
    | true =>
      simp only [d222453, d223995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222454 q = 0) : d223996 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222454, d223996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222454, d223996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222455 q = 0) : d223997 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222455, d223997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222455, d223997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222456 q = 0) : d223998 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222456, d223998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222456, d223998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222457 q = 0) : d223999 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222457, d223999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222457, d223999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222458 q = 0) : d224000 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222458, d224000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222458, d224000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21851 (p : Pattern) (selected : d222464 p = 0) : d224006 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222459 q = 0) : d224001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222459, d224001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21850 q selected
    | true =>
      simp only [d222459, d224001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222460 q = 0) : d224002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222460, d224002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222460, d224002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222461 q = 0) : d224003 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222461, d224003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222461, d224003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222462 q = 0) : d224004 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222462, d224004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222462, d224004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222463 q = 0) : d224005 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222463, d224005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222463, d224005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222464 q = 0) : d224006 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222464, d224006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222464, d224006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21852 (p : Pattern) (selected : d222470 p = 0) : d224118 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222451 q = 0) : d224113 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222451, d224113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21848 q selected
    | true =>
      simp only [d222451, d224113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21825 q selected
  have h2 (q : Pattern) (selected : d222465 q = 0) : d224007 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222465, d224007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21851 q selected
    | true =>
      simp only [d222465, d224007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d222466 q = 0) : d224114 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222466, d224114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222466, d224114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222329 q = 0) : d224007 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222329, d224007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21825 q selected
    | true =>
      simp only [d222329, d224007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222330 q = 0) : d224008 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222330, d224008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222330, d224008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222467 q = 0) : d224115 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222467, d224115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222467, d224115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222468 q = 0) : d224116 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222468, d224116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222468, d224116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222469 q = 0) : d224117 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222469, d224117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222469, d224117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d222470 q = 0) : d224118 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222470, d224118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222470, d224118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21853 (p : Pattern) (selected : d222476 p = 0) : d224124 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222351 q = 0) : d224029 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222351, d224029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222351, d224029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21828 q selected
  have h2 (q : Pattern) (selected : d222352 q = 0) : d224030 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222352, d224030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222352, d224030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d222358 q = 0) : d224036 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222358, d224036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21828 q selected
    | true =>
      simp only [d222358, d224036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21829 q selected
  have h4 (q : Pattern) (selected : d222359 q = 0) : d224037 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222359, d224037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222359, d224037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222360 q = 0) : d224038 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222360, d224038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222360, d224038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222424 q = 0) : d224086 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222424, d224086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21838 q selected
    | true =>
      simp only [d222424, d224086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21843 q selected
  have h7 (q : Pattern) (selected : d222426 q = 0) : d224088 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222426, d224088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21844 q selected
    | true =>
      simp only [d222426, d224088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222427 q = 0) : d224089 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222427, d224089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222427, d224089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d222428 q = 0) : d224090 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222428, d224090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222428, d224090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d222429 q = 0) : d224091 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222429, d224091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222429, d224091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222433 q = 0) : d224095 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222433, d224095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222433, d224095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21845 q selected
  have h12 (q : Pattern) (selected : d222434 q = 0) : d224096 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222434, d224096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d222434, d224096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d222435 q = 0) : d224097 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222435, d224097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d222435, d224097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d222436 q = 0) : d224098 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222436, d224098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d222436, d224098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d222437 q = 0) : d224099 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d222437, d224099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222437, d224099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d222471 q = 0) : d224119 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222471, d224119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222471, d224119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21852 q selected
  have h17 (q : Pattern) (selected : d222472 q = 0) : d224120 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222472, d224120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d222472, d224120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d222473 q = 0) : d224121 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222473, d224121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d222473, d224121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d222474 q = 0) : d224122 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222474, d224122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d222474, d224122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d222475 q = 0) : d224123 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d222475, d224123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d222475, d224123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d222476 q = 0) : d224124 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d222476, d224124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d222476, d224124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro21854 (p : Pattern) (selected : d222482 p = 0) : d224130 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222341 q = 0) : d224019 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d222341, d224019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222341, d224019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21827 q selected
  have h2 (q : Pattern) (selected : d222342 q = 0) : d224020 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d222342, d224020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222342, d224020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222343 q = 0) : d224021 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d222343, d224021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222343, d224021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222344 q = 0) : d224022 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d222344, d224022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222344, d224022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222345 q = 0) : d224023 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d222345, d224023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222345, d224023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222477 q = 0) : d224125 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d222477, d224125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222477, d224125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21853 q selected
  have h7 (q : Pattern) (selected : d222478 q = 0) : d224126 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d222478, d224126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222478, d224126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222479 q = 0) : d224127 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d222479, d224127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222479, d224127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d222480 q = 0) : d224128 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d222480, d224128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222480, d224128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222481 q = 0) : d224129 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d222481, d224129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222481, d224129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222482 q = 0) : d224130 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d222482, d224130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222482, d224130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21855 (p : Pattern) (selected : d222487 p = 0) : d224135 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222386 q = 0) : d224064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222386, d224064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21834 q selected
    | true =>
      simp only [d222386, d224064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21818 q selected
  have h2 (q : Pattern) (selected : d222483 q = 0) : d224131 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222483, d224131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222483, d224131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222484 q = 0) : d224132 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222484, d224132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222484, d224132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222485 q = 0) : d224133 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222485, d224133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222485, d224133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222486 q = 0) : d224134 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222486, d224134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222486, d224134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222487 q = 0) : d224135 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222487, d224135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222487, d224135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21856 (p : Pattern) (selected : d222494 p = 0) : d224142 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222386 q = 0) : d224064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222386, d224064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21834 q selected
    | true =>
      simp only [d222386, d224064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21818 q selected
  have h2 (q : Pattern) (selected : d222483 q = 0) : d224131 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222483, d224131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222483, d224131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222484 q = 0) : d224132 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222484, d224132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222484, d224132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222485 q = 0) : d224133 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222485, d224133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222485, d224133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222486 q = 0) : d224134 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222486, d224134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222486, d224134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222416 q = 0) : d224080 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222416, d224080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21841 q selected
    | true =>
      simp only [d222416, d224080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21820 q selected
  have h7 (q : Pattern) (selected : d222490 q = 0) : d224138 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222490, d224138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222490, d224138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222491 q = 0) : d224139 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222491, d224139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222491, d224139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222492 q = 0) : d224140 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222492, d224140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222492, d224140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222493 q = 0) : d224141 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222493, d224141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222493, d224141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222494 q = 0) : d224142 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222494, d224142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222494, d224142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21857 (p : Pattern) (selected : d222499 p = 0) : d224147 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222380 q = 0) : d224058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21833 q selected
    | true =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222381 q = 0) : d224059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222287 q = 0) : d223965 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21817 q selected
    | true =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222288 q = 0) : d223966 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222382 q = 0) : d224060 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222382, d224060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222382, d224060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222383 q = 0) : d224061 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222383, d224061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222383, d224061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222498 q = 0) : d224146 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222498, d224146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222498, d224146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222499 q = 0) : d224147 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222499, d224147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222499, d224147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21858 (p : Pattern) (selected : d222506 p = 0) : d224154 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222380 q = 0) : d224058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21833 q selected
    | true =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222381 q = 0) : d224059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222287 q = 0) : d223965 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21817 q selected
    | true =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222288 q = 0) : d223966 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222382 q = 0) : d224060 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222382, d224060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222382, d224060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222504 q = 0) : d224152 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222504, d224152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222504, d224152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222505 q = 0) : d224153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222505, d224153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222505, d224153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222506 q = 0) : d224154 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222506, d224154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222506, d224154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21859 (p : Pattern) (selected : d222512 p = 0) : d224160 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117008 q = 0) : d118831 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117008, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8876 q selected
    | true =>
      simp only [d117008, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117009 q = 0) : d118832 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117009, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117009, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117010 q = 0) : d118833 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117010, d118833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117010, d118833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117011 q = 0) : d118834 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117011, d118834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117011, d118834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117227 q = 0) : d119012 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8921 q selected
    | true =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117228 q = 0) : d119013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117229 q = 0) : d119014 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117229, d119014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117229, d119014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117230 q = 0) : d119015 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117230, d119015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117230, d119015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222510 q = 0) : d224158 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222510, d224158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222510, d224158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116754 q = 0) : d118615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8830 q selected
    | true =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d116755 q = 0) : d118616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d116756 q = 0) : d118617 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116756, d118617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116756, d118617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d116757 q = 0) : d118618 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116757, d118618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d116757, d118618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d222511 q = 0) : d224159 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222511, d224159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222511, d224159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d222512 q = 0) : d224160 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222512, d224160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222512, d224160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21860 (p : Pattern) (selected : d222518 p = 0) : d224166 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222513 q = 0) : d224161 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222513, d224161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21859 q selected
    | true =>
      simp only [d222513, d224161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21832 q selected
  have h2 (q : Pattern) (selected : d222514 q = 0) : d224162 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222514, d224162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222514, d224162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222515 q = 0) : d224163 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222515, d224163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222515, d224163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222374 q = 0) : d224052 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222374, d224052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21832 q selected
    | true =>
      simp only [d222374, d224052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21816 q selected
  have h5 (q : Pattern) (selected : d222375 q = 0) : d224053 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222375, d224053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222375, d224053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222376 q = 0) : d224054 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222376, d224054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222376, d224054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222516 q = 0) : d224164 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222516, d224164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222516, d224164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222281 q = 0) : d223959 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222281, d223959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21816 q selected
    | true =>
      simp only [d222281, d223959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222282 q = 0) : d223960 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222282, d223960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222282, d223960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222283 q = 0) : d223961 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222283, d223961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222283, d223961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222377 q = 0) : d224055 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222377, d224055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222377, d224055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d222517 q = 0) : d224165 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222517, d224165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222517, d224165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d222518 q = 0) : d224166 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222518, d224166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d222518, d224166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro21861 (p : Pattern) (selected : d222524 p = 0) : d224172 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222519 q = 0) : d224167 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222519, d224167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21860 q selected
    | true =>
      simp only [d222519, d224167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222520 q = 0) : d224168 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222520, d224168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222520, d224168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222380 q = 0) : d224058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21833 q selected
    | true =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222381 q = 0) : d224059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222521 q = 0) : d224169 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222521, d224169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222521, d224169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222522 q = 0) : d224170 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222522, d224170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222522, d224170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222523 q = 0) : d224171 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222523, d224171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222523, d224171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222524 q = 0) : d224172 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222524, d224172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222524, d224172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21862 (p : Pattern) (selected : d222526 p = 0) : d224051 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117026 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8880 q selected
    | true =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117027 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117028 q = 0) : d118718 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117028, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117028, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117029 q = 0) : d118719 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117029, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117029, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116873 q = 0) : d118615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116873, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8851 q selected
    | true =>
      simp only [d116873, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116874 q = 0) : d118616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116874, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116874, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116875 q = 0) : d118617 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116875, d118617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116875, d118617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116876 q = 0) : d118618 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116876, d118618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116876, d118618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117030 q = 0) : d118720 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117030, d118720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117030, d118720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116877 q = 0) : d118619 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116877, d118619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d116877, d118619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d222526 q = 0) : d224051 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222526, d224051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222526, d224051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21863 (p : Pattern) (selected : d222532 p = 0) : d224057 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222527 q = 0) : d224052 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222527, d224052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21862 q selected
    | true =>
      simp only [d222527, d224052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21835 q selected
  have h2 (q : Pattern) (selected : d222528 q = 0) : d224053 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222528, d224053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222528, d224053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222529 q = 0) : d224054 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222529, d224054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222529, d224054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222388 q = 0) : d223959 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222388, d223959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21835 q selected
    | true =>
      simp only [d222388, d223959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222389 q = 0) : d223960 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222389, d223960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222389, d223960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222390 q = 0) : d223961 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222390, d223961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222390, d223961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222530 q = 0) : d224055 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222530, d224055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222530, d224055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222391 q = 0) : d223962 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222391, d223962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222391, d223962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222531 q = 0) : d224056 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222531, d224056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222531, d224056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222532 q = 0) : d224057 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222532, d224057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222532, d224057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21864 (p : Pattern) (selected : d222538 p = 0) : d224063 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222533 q = 0) : d224058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222533, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21863 q selected
    | true =>
      simp only [d222533, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222534 q = 0) : d224059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222534, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222534, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222394 q = 0) : d223965 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222394, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21836 q selected
    | true =>
      simp only [d222394, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222395 q = 0) : d223966 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222395, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222395, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222535 q = 0) : d224060 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222535, d224060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222535, d224060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222536 q = 0) : d224061 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222536, d224061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222536, d224061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222537 q = 0) : d224062 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222537, d224062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222537, d224062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222538 q = 0) : d224063 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222538, d224063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222538, d224063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21865 (p : Pattern) (selected : d222544 p = 0) : d224178 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222380 q = 0) : d224058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21833 q selected
    | true =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222381 q = 0) : d224059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222541 q = 0) : d224175 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222541, d224175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222541, d224175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222542 q = 0) : d224176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222542, d224176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222542, d224176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222543 q = 0) : d224177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222543, d224177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222543, d224177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222544 q = 0) : d224178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222544, d224178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222544, d224178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21866 (p : Pattern) (selected : d222550 p = 0) : d224184 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222500 q = 0) : d224148 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222500, d224148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21857 q selected
    | true =>
      simp only [d222500, d224148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21830 q selected
  have h2 (q : Pattern) (selected : d222501 q = 0) : d224149 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222501, d224149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222501, d224149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222502 q = 0) : d224150 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222502, d224150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222502, d224150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222503 q = 0) : d224151 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222503, d224151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222503, d224151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222507 q = 0) : d224155 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222507, d224155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21858 q selected
    | true =>
      simp only [d222507, d224155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21831 q selected
  have h6 (q : Pattern) (selected : d222508 q = 0) : d224156 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222508, d224156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222508, d224156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222509 q = 0) : d224157 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222509, d224157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222509, d224157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222525 q = 0) : d224173 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222525, d224173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21861 q selected
    | true =>
      simp only [d222525, d224173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21834 q selected
  have h9 (q : Pattern) (selected : d222539 q = 0) : d224064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222539, d224064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21864 q selected
    | true =>
      simp only [d222539, d224064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21837 q selected
  have h10 (q : Pattern) (selected : d222540 q = 0) : d224174 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222540, d224174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222540, d224174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222545 q = 0) : d224179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222545, d224179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21865 q selected
    | true =>
      simp only [d222545, d224179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d222546 q = 0) : d224180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222546, d224180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d222546, d224180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d222547 q = 0) : d224181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222547, d224181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222547, d224181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d222548 q = 0) : d224182 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222548, d224182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222548, d224182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d222549 q = 0) : d224183 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222549, d224183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222549, d224183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d222550 q = 0) : d224184 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222550, d224184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222550, d224184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro21867 (p : Pattern) (selected : d222551 p = 0) : d224185 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222380 q = 0) : d224058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21833 q selected
    | true =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222381 q = 0) : d224059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222287 q = 0) : d223965 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21817 q selected
    | true =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222288 q = 0) : d223966 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222382 q = 0) : d224060 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222382, d224060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222382, d224060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222383 q = 0) : d224061 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222383, d224061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222383, d224061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222498 q = 0) : d224146 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222498, d224146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222498, d224146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222551 q = 0) : d224185 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222551, d224185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222551, d224185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21868 (p : Pattern) (selected : d222556 p = 0) : d224190 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222380 q = 0) : d224058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21833 q selected
    | true =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222381 q = 0) : d224059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222287 q = 0) : d223965 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21817 q selected
    | true =>
      simp only [d222287, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222288 q = 0) : d223966 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222288, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222382 q = 0) : d224060 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222382, d224060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222382, d224060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222504 q = 0) : d224152 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222504, d224152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222504, d224152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222505 q = 0) : d224153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222505, d224153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222505, d224153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222556 q = 0) : d224190 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222556, d224190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222556, d224190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21869 (p : Pattern) (selected : d222560 p = 0) : d224194 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222519 q = 0) : d224167 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222519, d224167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21860 q selected
    | true =>
      simp only [d222519, d224167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222520 q = 0) : d224168 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222520, d224168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222520, d224168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222380 q = 0) : d224058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21833 q selected
    | true =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222381 q = 0) : d224059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222521 q = 0) : d224169 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222521, d224169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222521, d224169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222522 q = 0) : d224170 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222522, d224170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222522, d224170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222523 q = 0) : d224171 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222523, d224171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222523, d224171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222560 q = 0) : d224194 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222560, d224194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222560, d224194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21870 (p : Pattern) (selected : d222562 p = 0) : d224079 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222533 q = 0) : d224058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222533, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21863 q selected
    | true =>
      simp only [d222533, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222534 q = 0) : d224059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222534, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222534, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222394 q = 0) : d223965 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222394, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21836 q selected
    | true =>
      simp only [d222394, d223965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222395 q = 0) : d223966 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222395, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222395, d223966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222535 q = 0) : d224060 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222535, d224060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222535, d224060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222536 q = 0) : d224061 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222536, d224061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222536, d224061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222537 q = 0) : d224062 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222537, d224062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222537, d224062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222562 q = 0) : d224079 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222562, d224079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222562, d224079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21871 (p : Pattern) (selected : d222565 p = 0) : d224197 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222380 q = 0) : d224058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21833 q selected
    | true =>
      simp only [d222380, d224058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222381 q = 0) : d224059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222381, d224059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222541 q = 0) : d224175 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222541, d224175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222541, d224175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222542 q = 0) : d224176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222542, d224176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222542, d224176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222543 q = 0) : d224177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222543, d224177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222543, d224177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222565 q = 0) : d224197 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222565, d224197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222565, d224197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21872 (p : Pattern) (selected : d222571 p = 0) : d224203 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222500 q = 0) : d224148 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222500, d224148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21857 q selected
    | true =>
      simp only [d222500, d224148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21830 q selected
  have h2 (q : Pattern) (selected : d222501 q = 0) : d224149 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222501, d224149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222501, d224149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222502 q = 0) : d224150 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222502, d224150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222502, d224150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222503 q = 0) : d224151 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222503, d224151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222503, d224151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222507 q = 0) : d224155 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222507, d224155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21858 q selected
    | true =>
      simp only [d222507, d224155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21831 q selected
  have h6 (q : Pattern) (selected : d222508 q = 0) : d224156 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222508, d224156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222508, d224156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222509 q = 0) : d224157 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222509, d224157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222509, d224157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222525 q = 0) : d224173 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222525, d224173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21861 q selected
    | true =>
      simp only [d222525, d224173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21834 q selected
  have h9 (q : Pattern) (selected : d222539 q = 0) : d224064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222539, d224064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21864 q selected
    | true =>
      simp only [d222539, d224064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21837 q selected
  have h10 (q : Pattern) (selected : d222540 q = 0) : d224174 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222540, d224174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222540, d224174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222545 q = 0) : d224179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222545, d224179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21865 q selected
    | true =>
      simp only [d222545, d224179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d222546 q = 0) : d224180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222546, d224180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d222546, d224180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d222547 q = 0) : d224181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222547, d224181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222547, d224181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d222548 q = 0) : d224182 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222548, d224182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222548, d224182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d222549 q = 0) : d224183 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222549, d224183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222549, d224183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d222552 q = 0) : d224186 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222552, d224186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21867 q selected
    | true =>
      simp only [d222552, d224186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21839 q selected
  have h17 (q : Pattern) (selected : d222553 q = 0) : d224187 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222553, d224187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222553, d224187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d222554 q = 0) : d224188 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222554, d224188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d222554, d224188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d222555 q = 0) : d224189 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222555, d224189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222555, d224189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d222557 q = 0) : d224191 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222557, d224191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21868 q selected
    | true =>
      simp only [d222557, d224191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21840 q selected
  have h21 (q : Pattern) (selected : d222558 q = 0) : d224192 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222558, d224192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222558, d224192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d222559 q = 0) : d224193 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222559, d224193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d222559, d224193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d222561 q = 0) : d224195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222561, d224195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21869 q selected
    | true =>
      simp only [d222561, d224195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21841 q selected
  have h24 (q : Pattern) (selected : d222563 q = 0) : d224080 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222563, d224080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21870 q selected
    | true =>
      simp only [d222563, d224080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21842 q selected
  have h25 (q : Pattern) (selected : d222564 q = 0) : d224196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222564, d224196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d222564, d224196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d222566 q = 0) : d224198 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222566, d224198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21871 q selected
    | true =>
      simp only [d222566, d224198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d222567 q = 0) : d224199 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222567, d224199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d222567, d224199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d222568 q = 0) : d224200 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222568, d224200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d222568, d224200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d222569 q = 0) : d224201 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222569, d224201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d222569, d224201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d222570 q = 0) : d224202 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222570, d224202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d222570, d224202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d222571 q = 0) : d224203 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222571, d224203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d222571, d224203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro21873 (p : Pattern) (selected : d222573 p = 0) : d224205 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222386 q = 0) : d224064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222386, d224064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21834 q selected
    | true =>
      simp only [d222386, d224064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21818 q selected
  have h2 (q : Pattern) (selected : d222483 q = 0) : d224131 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222483, d224131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222483, d224131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222484 q = 0) : d224132 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222484, d224132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222484, d224132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222485 q = 0) : d224133 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222485, d224133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222485, d224133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222486 q = 0) : d224134 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222486, d224134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222486, d224134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222293 q = 0) : d223971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222293, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21818 q selected
    | true =>
      simp only [d222293, d223971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222346 q = 0) : d224024 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222346, d224024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222346, d224024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222347 q = 0) : d224025 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222347, d224025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222347, d224025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222348 q = 0) : d224026 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222348, d224026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222348, d224026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222349 q = 0) : d224027 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222349, d224027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222349, d224027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222573 q = 0) : d224205 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222573, d224205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222573, d224205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21874 (p : Pattern) (selected : d222580 p = 0) : d224212 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222561 q = 0) : d224195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222561, d224195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21869 q selected
    | true =>
      simp only [d222561, d224195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21841 q selected
  have h2 (q : Pattern) (selected : d222563 q = 0) : d224080 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222563, d224080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21870 q selected
    | true =>
      simp only [d222563, d224080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21842 q selected
  have h3 (q : Pattern) (selected : d222564 q = 0) : d224196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222564, d224196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222564, d224196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222566 q = 0) : d224198 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222566, d224198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21871 q selected
    | true =>
      simp only [d222566, d224198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222567 q = 0) : d224199 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222567, d224199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222567, d224199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222568 q = 0) : d224200 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222568, d224200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222568, d224200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222578 q = 0) : d224210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222578, d224210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222578, d224210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222579 q = 0) : d224211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222579, d224211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222579, d224211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d222580 q = 0) : d224212 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222580, d224212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222580, d224212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21875 (p : Pattern) (selected : d222582 p = 0) : d224214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222300 q = 0) : d223978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222300, d223978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21820 q selected
    | true =>
      simp only [d222300, d223978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222353 q = 0) : d224031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222353, d224031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222353, d224031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222354 q = 0) : d224032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222354, d224032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222354, d224032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222355 q = 0) : d224033 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222355, d224033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222355, d224033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222356 q = 0) : d224034 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222356, d224034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222356, d224034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222582 q = 0) : d224214 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222582, d224214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222582, d224214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21876 (p : Pattern) (selected : d222590 p = 0) : d224222 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117092 q = 0) : d118895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117092, d118895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117092, d118895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8876 q selected
  have h2 (q : Pattern) (selected : d117008 q = 0) : d118831 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117008, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8876 q selected
    | true =>
      simp only [d117008, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117093 q = 0) : d118896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117093, d118896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117093, d118896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117009 q = 0) : d118832 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117009, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117009, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117094 q = 0) : d118897 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117094, d118897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117094, d118897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117095 q = 0) : d118898 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117095, d118898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117095, d118898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117346 q = 0) : d119097 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117346, d119097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117346, d119097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8921 q selected
  have h8 (q : Pattern) (selected : d117227 q = 0) : d119012 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8921 q selected
    | true =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117347 q = 0) : d119098 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117347, d119098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117347, d119098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117228 q = 0) : d119013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117348 q = 0) : d119099 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117348, d119099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117348, d119099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117349 q = 0) : d119100 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117349, d119100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117349, d119100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d222588 q = 0) : d224220 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222588, d224220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222588, d224220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d116794 q = 0) : d118655 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116794, d118655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116794, d118655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8830 q selected
  have h15 (q : Pattern) (selected : d116754 q = 0) : d118615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8830 q selected
    | true =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d116795 q = 0) : d118656 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116795, d118656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d116795, d118656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d116755 q = 0) : d118616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d116796 q = 0) : d118657 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116796, d118657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d116796, d118657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d116797 q = 0) : d118658 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116797, d118658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d116797, d118658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d222589 q = 0) : d224221 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222589, d224221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d222589, d224221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d222590 q = 0) : d224222 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222590, d224222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d222590, d224222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro21877 (p : Pattern) (selected : d222596 p = 0) : d224228 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222591 q = 0) : d224223 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222591, d224223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21876 q selected
    | true =>
      simp only [d222591, d224223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21846 q selected
  have h2 (q : Pattern) (selected : d222592 q = 0) : d224224 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222592, d224224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222592, d224224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222593 q = 0) : d224225 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222593, d224225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222593, d224225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222439 q = 0) : d224101 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222439, d224101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21846 q selected
    | true =>
      simp only [d222439, d224101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21823 q selected
  have h5 (q : Pattern) (selected : d222440 q = 0) : d224102 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222440, d224102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222440, d224102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222441 q = 0) : d224103 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222441, d224103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222441, d224103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222594 q = 0) : d224226 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222594, d224226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222594, d224226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222317 q = 0) : d223995 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222317, d223995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21823 q selected
    | true =>
      simp only [d222317, d223995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222318 q = 0) : d223996 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222318, d223996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222318, d223996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222319 q = 0) : d223997 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222319, d223997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222319, d223997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222442 q = 0) : d224104 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222442, d224104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222442, d224104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d222595 q = 0) : d224227 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222595, d224227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222595, d224227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d222596 q = 0) : d224228 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222596, d224228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d222596, d224228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro21878 (p : Pattern) (selected : d222602 p = 0) : d224234 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222597 q = 0) : d224229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222597, d224229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21877 q selected
    | true =>
      simp only [d222597, d224229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222598 q = 0) : d224230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222598, d224230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222598, d224230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222445 q = 0) : d224107 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222445, d224107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21847 q selected
    | true =>
      simp only [d222445, d224107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222446 q = 0) : d224108 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222446, d224108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222446, d224108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222599 q = 0) : d224231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222599, d224231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222599, d224231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222600 q = 0) : d224232 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222600, d224232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222600, d224232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222601 q = 0) : d224233 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222601, d224233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222601, d224233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222602 q = 0) : d224234 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222602, d224234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222602, d224234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21879 (p : Pattern) (selected : d222604 p = 0) : d224100 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117110 q = 0) : d118769 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117110, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117110, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8880 q selected
  have h2 (q : Pattern) (selected : d117026 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8880 q selected
    | true =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117111 q = 0) : d118770 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117111, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117111, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117027 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117112 q = 0) : d118771 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117112, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117112, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117113 q = 0) : d118772 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117113, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117113, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116946 q = 0) : d118655 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116946, d118655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116946, d118655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8851 q selected
  have h8 (q : Pattern) (selected : d116873 q = 0) : d118615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116873, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8851 q selected
    | true =>
      simp only [d116873, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d116947 q = 0) : d118656 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116947, d118656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116947, d118656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116874 q = 0) : d118616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116874, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d116874, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d116948 q = 0) : d118657 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116948, d118657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d116948, d118657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d116949 q = 0) : d118658 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116949, d118658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d116949, d118658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117114 q = 0) : d118773 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117114, d118773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117114, d118773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d116950 q = 0) : d118659 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116950, d118659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d116950, d118659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d222604 q = 0) : d224100 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222604, d224100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d222604, d224100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21880 (p : Pattern) (selected : d222610 p = 0) : d224106 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222605 q = 0) : d224101 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222605, d224101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21879 q selected
    | true =>
      simp only [d222605, d224101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21849 q selected
  have h2 (q : Pattern) (selected : d222606 q = 0) : d224102 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222606, d224102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222606, d224102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222607 q = 0) : d224103 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222607, d224103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222607, d224103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222453 q = 0) : d223995 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222453, d223995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21849 q selected
    | true =>
      simp only [d222453, d223995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222454 q = 0) : d223996 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222454, d223996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222454, d223996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222455 q = 0) : d223997 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222455, d223997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222455, d223997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222608 q = 0) : d224104 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222608, d224104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222608, d224104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222456 q = 0) : d223998 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222456, d223998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222456, d223998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222609 q = 0) : d224105 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222609, d224105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222609, d224105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222610 q = 0) : d224106 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222610, d224106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222610, d224106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21881 (p : Pattern) (selected : d222616 p = 0) : d224112 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222611 q = 0) : d224107 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222611, d224107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21880 q selected
    | true =>
      simp only [d222611, d224107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222612 q = 0) : d224108 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222612, d224108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222612, d224108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222459 q = 0) : d224001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222459, d224001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21850 q selected
    | true =>
      simp only [d222459, d224001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222460 q = 0) : d224002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222460, d224002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222460, d224002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222613 q = 0) : d224109 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222613, d224109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222613, d224109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222614 q = 0) : d224110 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222614, d224110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222614, d224110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222615 q = 0) : d224111 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222615, d224111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222615, d224111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222616 q = 0) : d224112 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222616, d224112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222616, d224112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21882 (p : Pattern) (selected : d222622 p = 0) : d224240 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222445 q = 0) : d224107 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222445, d224107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21847 q selected
    | true =>
      simp only [d222445, d224107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222446 q = 0) : d224108 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222446, d224108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222446, d224108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222619 q = 0) : d224237 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222619, d224237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222619, d224237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222620 q = 0) : d224238 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222620, d224238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222620, d224238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222621 q = 0) : d224239 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222621, d224239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222621, d224239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222622 q = 0) : d224240 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222622, d224240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222622, d224240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21883 (p : Pattern) (selected : d222628 p = 0) : d224246 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222603 q = 0) : d224235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222603, d224235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21878 q selected
    | true =>
      simp only [d222603, d224235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21848 q selected
  have h2 (q : Pattern) (selected : d222617 q = 0) : d224113 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222617, d224113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21881 q selected
    | true =>
      simp only [d222617, d224113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21851 q selected
  have h3 (q : Pattern) (selected : d222618 q = 0) : d224236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222618, d224236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222618, d224236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222623 q = 0) : d224241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222623, d224241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21882 q selected
    | true =>
      simp only [d222623, d224241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222624 q = 0) : d224242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222624, d224242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222624, d224242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222625 q = 0) : d224243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222625, d224243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222625, d224243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222626 q = 0) : d224244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222626, d224244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222626, d224244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222627 q = 0) : d224245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222627, d224245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222627, d224245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d222628 q = 0) : d224246 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222628, d224246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222628, d224246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21884 (p : Pattern) (selected : d222634 p = 0) : d224252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222329 q = 0) : d224007 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222329, d224007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21825 q selected
    | true =>
      simp only [d222329, d224007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222630 q = 0) : d224248 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222630, d224248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222630, d224248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222631 q = 0) : d224249 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222631, d224249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222631, d224249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222632 q = 0) : d224250 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222632, d224250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222632, d224250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222633 q = 0) : d224251 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222633, d224251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222633, d224251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222634 q = 0) : d224252 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222634, d224252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222634, d224252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21885 (p : Pattern) (selected : d222640 p = 0) : d224258 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222488 q = 0) : d224136 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222488, d224136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222488, d224136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21855 q selected
  have h2 (q : Pattern) (selected : d222489 q = 0) : d224137 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222489, d224137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222489, d224137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d222495 q = 0) : d224143 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222495, d224143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21855 q selected
    | true =>
      simp only [d222495, d224143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21856 q selected
  have h4 (q : Pattern) (selected : d222496 q = 0) : d224144 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222496, d224144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222496, d224144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222497 q = 0) : d224145 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222497, d224145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222497, d224145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222572 q = 0) : d224204 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222572, d224204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21866 q selected
    | true =>
      simp only [d222572, d224204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21872 q selected
  have h7 (q : Pattern) (selected : d222574 q = 0) : d224206 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222574, d224206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21873 q selected
    | true =>
      simp only [d222574, d224206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21829 q selected
  have h8 (q : Pattern) (selected : d222575 q = 0) : d224207 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222575, d224207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222575, d224207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d222576 q = 0) : d224208 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222576, d224208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222576, d224208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d222577 q = 0) : d224209 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222577, d224209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222577, d224209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222581 q = 0) : d224213 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222581, d224213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222581, d224213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21874 q selected
  have h12 (q : Pattern) (selected : d222583 q = 0) : d224215 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222583, d224215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222583, d224215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21875 q selected
  have h13 (q : Pattern) (selected : d222584 q = 0) : d224216 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222584, d224216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d222584, d224216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d222585 q = 0) : d224217 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222585, d224217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d222585, d224217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d222586 q = 0) : d224218 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222586, d224218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d222586, d224218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d222587 q = 0) : d224219 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d222587, d224219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222587, d224219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d222629 q = 0) : d224247 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222629, d224247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222629, d224247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21883 q selected
  have h18 (q : Pattern) (selected : d222635 q = 0) : d224253 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222635, d224253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222635, d224253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21884 q selected
  have h19 (q : Pattern) (selected : d222636 q = 0) : d224254 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222636, d224254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d222636, d224254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d222637 q = 0) : d224255 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222637, d224255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d222637, d224255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d222638 q = 0) : d224256 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222638, d224256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d222638, d224256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d222639 q = 0) : d224257 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d222639, d224257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d222639, d224257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d222640 q = 0) : d224258 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d222640, d224258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d222640, d224258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro21886 (p : Pattern) (selected : d222646 p = 0) : d224264 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222641 q = 0) : d224259 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d222641, d224259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222641, d224259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21885 q selected
  have h2 (q : Pattern) (selected : d222642 q = 0) : d224260 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d222642, d224260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222642, d224260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222643 q = 0) : d224261 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d222643, d224261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222643, d224261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222644 q = 0) : d224262 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d222644, d224262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222644, d224262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222645 q = 0) : d224263 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d222645, d224263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222645, d224263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222646 q = 0) : d224264 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d222646, d224264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222646, d224264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21887 (p : Pattern) (selected : d222648 p = 0) : d224266 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117008 q = 0) : d118831 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117008, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8876 q selected
    | true =>
      simp only [d117008, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117009 q = 0) : d118832 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117009, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117009, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117010 q = 0) : d118833 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117010, d118833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117010, d118833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117011 q = 0) : d118834 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117011, d118834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117011, d118834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117227 q = 0) : d119012 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8921 q selected
    | true =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117228 q = 0) : d119013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117229 q = 0) : d119014 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117229, d119014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117229, d119014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117230 q = 0) : d119015 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117230, d119015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117230, d119015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222510 q = 0) : d224158 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222510, d224158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222510, d224158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117231 q = 0) : d119016 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117231, d119016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117231, d119016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d222648 q = 0) : d224266 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222648, d224266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222648, d224266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21888 (p : Pattern) (selected : d222649 p = 0) : d224267 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116855 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8847 q selected
    | true =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116856 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116857 q = 0) : d118718 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116857, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116857, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116858 q = 0) : d118719 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116858, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116858, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117158 q = 0) : d118943 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117158, d118943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117158, d118943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222649 q = 0) : d224267 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222649, d224267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222649, d224267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21889 (p : Pattern) (selected : d222659 p = 0) : d224277 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222650 q = 0) : d224268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222650, d224268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21887 q selected
    | true =>
      simp only [d222650, d224268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21888 q selected
  have h2 (q : Pattern) (selected : d222651 q = 0) : d224269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222651, d224269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222651, d224269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222652 q = 0) : d224270 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222652, d224270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222652, d224270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222653 q = 0) : d224271 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222653, d224271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21888 q selected
    | true =>
      simp only [d222653, d224271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222654 q = 0) : d224272 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222654, d224272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222654, d224272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222655 q = 0) : d224273 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222655, d224273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222655, d224273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222656 q = 0) : d224274 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222656, d224274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222656, d224274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222657 q = 0) : d224275 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222657, d224275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222657, d224275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222658 q = 0) : d224276 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222658, d224276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222658, d224276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222659 q = 0) : d224277 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222659, d224277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222659, d224277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21890 (p : Pattern) (selected : d222663 p = 0) : d224281 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222653 q = 0) : d224271 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222653, d224271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21888 q selected
    | true =>
      simp only [d222653, d224271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222654 q = 0) : d224272 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222654, d224272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222654, d224272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222655 q = 0) : d224273 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222655, d224273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222655, d224273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222657 q = 0) : d224275 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222657, d224275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222657, d224275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222662 q = 0) : d224280 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222662, d224280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222662, d224280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222663 q = 0) : d224281 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222663, d224281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222663, d224281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21891 (p : Pattern) (selected : d222669 p = 0) : d224287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222660 q = 0) : d224278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21889 q selected
    | true =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222661 q = 0) : d224279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222664 q = 0) : d224282 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21890 q selected
    | true =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222665 q = 0) : d224283 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222666 q = 0) : d224284 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222666, d224284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222666, d224284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222667 q = 0) : d224285 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222667, d224285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222667, d224285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222668 q = 0) : d224286 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222668, d224286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222668, d224286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222669 q = 0) : d224287 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222669, d224287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222669, d224287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21892 (p : Pattern) (selected : d222673 p = 0) : d224291 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222664 q = 0) : d224282 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21890 q selected
    | true =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222665 q = 0) : d224283 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222670 q = 0) : d224288 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222670, d224288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222670, d224288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222671 q = 0) : d224289 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222671, d224289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222671, d224289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222672 q = 0) : d224290 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222672, d224290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222672, d224290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222673 q = 0) : d224291 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222673, d224291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222673, d224291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21893 (p : Pattern) (selected : d222679 p = 0) : d224297 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222674 q = 0) : d224292 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222674, d224292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21891 q selected
    | true =>
      simp only [d222674, d224292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21892 q selected
  have h2 (q : Pattern) (selected : d222675 q = 0) : d224293 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222675, d224293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222675, d224293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222676 q = 0) : d224294 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222676, d224294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222676, d224294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222677 q = 0) : d224295 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222677, d224295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222677, d224295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222678 q = 0) : d224296 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222678, d224296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222678, d224296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222679 q = 0) : d224297 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222679, d224297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222679, d224297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21894 (p : Pattern) (selected : d222682 p = 0) : d224300 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222660 q = 0) : d224278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21889 q selected
    | true =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222661 q = 0) : d224279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222664 q = 0) : d224282 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21890 q selected
    | true =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222665 q = 0) : d224283 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222666 q = 0) : d224284 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222666, d224284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222666, d224284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222667 q = 0) : d224285 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222667, d224285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222667, d224285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222668 q = 0) : d224286 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222668, d224286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222668, d224286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222682 q = 0) : d224300 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222682, d224300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222682, d224300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21895 (p : Pattern) (selected : d222683 p = 0) : d224301 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222664 q = 0) : d224282 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21890 q selected
    | true =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222665 q = 0) : d224283 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222670 q = 0) : d224288 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222670, d224288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222670, d224288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222671 q = 0) : d224289 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222671, d224289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222671, d224289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222672 q = 0) : d224290 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222672, d224290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222672, d224290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222683 q = 0) : d224301 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222683, d224301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222683, d224301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21896 (p : Pattern) (selected : d222689 p = 0) : d224307 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222674 q = 0) : d224292 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222674, d224292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21891 q selected
    | true =>
      simp only [d222674, d224292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21892 q selected
  have h2 (q : Pattern) (selected : d222675 q = 0) : d224293 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222675, d224293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222675, d224293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222676 q = 0) : d224294 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222676, d224294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222676, d224294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222677 q = 0) : d224295 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222677, d224295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222677, d224295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222678 q = 0) : d224296 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222678, d224296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222678, d224296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222684 q = 0) : d224302 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222684, d224302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21894 q selected
    | true =>
      simp only [d222684, d224302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21895 q selected
  have h7 (q : Pattern) (selected : d222685 q = 0) : d224303 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222685, d224303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222685, d224303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222686 q = 0) : d224304 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222686, d224304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222686, d224304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222687 q = 0) : d224305 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222687, d224305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222687, d224305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222688 q = 0) : d224306 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222688, d224306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222688, d224306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222689 q = 0) : d224307 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222689, d224307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222689, d224307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21897 (p : Pattern) (selected : d222694 p = 0) : d224312 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222660 q = 0) : d224278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21889 q selected
    | true =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222661 q = 0) : d224279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222664 q = 0) : d224282 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21890 q selected
    | true =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222665 q = 0) : d224283 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222666 q = 0) : d224284 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222666, d224284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222666, d224284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222667 q = 0) : d224285 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222667, d224285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222667, d224285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222693 q = 0) : d224311 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222693, d224311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222693, d224311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222694 q = 0) : d224312 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222694, d224312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222694, d224312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21898 (p : Pattern) (selected : d222696 p = 0) : d224314 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222664 q = 0) : d224282 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21890 q selected
    | true =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222665 q = 0) : d224283 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222670 q = 0) : d224288 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222670, d224288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222670, d224288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222671 q = 0) : d224289 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222671, d224289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222671, d224289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222695 q = 0) : d224313 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222695, d224313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222695, d224313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222696 q = 0) : d224314 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222696, d224314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222696, d224314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21899 (p : Pattern) (selected : d222703 p = 0) : d224321 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222660 q = 0) : d224278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21889 q selected
    | true =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222661 q = 0) : d224279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222664 q = 0) : d224282 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21890 q selected
    | true =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222665 q = 0) : d224283 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222666 q = 0) : d224284 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222666, d224284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222666, d224284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222701 q = 0) : d224319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222701, d224319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222701, d224319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222702 q = 0) : d224320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222702, d224320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222702, d224320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222703 q = 0) : d224321 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222703, d224321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222703, d224321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21900 (p : Pattern) (selected : d222706 p = 0) : d224324 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222664 q = 0) : d224282 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21890 q selected
    | true =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222665 q = 0) : d224283 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222670 q = 0) : d224288 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222670, d224288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222670, d224288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222704 q = 0) : d224322 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222704, d224322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222704, d224322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222705 q = 0) : d224323 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222705, d224323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222705, d224323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222706 q = 0) : d224324 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222706, d224324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222706, d224324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21901 (p : Pattern) (selected : d9585 p = 0) : d101165 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9581 q = 0) : d101161 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d101161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6640 q selected
    | true =>
      simp only [d9581, d101161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9582 q = 0) : d101162 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d101162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9582, d101162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9452 q = 0) : d101067 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2798 q selected
    | true =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9453 q = 0) : d101068 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9583 q = 0) : d101163 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9583, d101163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9583, d101163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9584 q = 0) : d101164 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9584, d101164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9584, d101164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9585 q = 0) : d101165 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9585, d101165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9585, d101165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro21902 (p : Pattern) (selected : d222716 p = 0) : d224334 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117219 q = 0) : d119004 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117219, d119004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8919 q selected
    | true =>
      simp only [d117219, d119004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117220 q = 0) : d119005 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117220, d119005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117220, d119005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117221 q = 0) : d119006 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117221, d119006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117221, d119006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117222 q = 0) : d119007 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117222, d119007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117222, d119007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222710 q = 0) : d224328 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d222710, d224328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21901 q selected
    | true =>
      simp only [d222710, d224328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222711 q = 0) : d224329 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d222711, d224329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222711, d224329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222712 q = 0) : d224330 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d222712, d224330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222712, d224330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222713 q = 0) : d224331 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d222713, d224331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222713, d224331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222714 q = 0) : d224332 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222714, d224332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222714, d224332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117227 q = 0) : d119012 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8921 q selected
    | true =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117228 q = 0) : d119013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117229 q = 0) : d119014 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117229, d119014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117229, d119014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117230 q = 0) : d119015 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117230, d119015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117230, d119015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d222715 q = 0) : d224333 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222715, d224333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222715, d224333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d222716 q = 0) : d224334 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222716, d224334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222716, d224334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21903 (p : Pattern) (selected : d222720 p = 0) : d224338 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117227 q = 0) : d119012 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8921 q selected
    | true =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117228 q = 0) : d119013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117229 q = 0) : d119014 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117229, d119014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117229, d119014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117230 q = 0) : d119015 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117230, d119015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117230, d119015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117231 q = 0) : d119016 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117231, d119016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117231, d119016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222720 q = 0) : d224338 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222720, d224338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222720, d224338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21904 (p : Pattern) (selected : d222726 p = 0) : d224344 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222717 q = 0) : d224335 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222717, d224335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21902 q selected
    | true =>
      simp only [d222717, d224335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21887 q selected
  have h2 (q : Pattern) (selected : d222718 q = 0) : d224336 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222718, d224336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222718, d224336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222719 q = 0) : d224337 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222719, d224337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222719, d224337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222721 q = 0) : d224339 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222721, d224339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21887 q selected
    | true =>
      simp only [d222721, d224339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21903 q selected
  have h5 (q : Pattern) (selected : d222722 q = 0) : d224340 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222722, d224340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222722, d224340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222723 q = 0) : d224341 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222723, d224341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222723, d224341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222724 q = 0) : d224342 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222724, d224342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222724, d224342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222650 q = 0) : d224268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222650, d224268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21887 q selected
    | true =>
      simp only [d222650, d224268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21888 q selected
  have h9 (q : Pattern) (selected : d222651 q = 0) : d224269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222651, d224269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222651, d224269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222652 q = 0) : d224270 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222652, d224270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222652, d224270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222653 q = 0) : d224271 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222653, d224271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21888 q selected
    | true =>
      simp only [d222653, d224271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d222654 q = 0) : d224272 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222654, d224272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222654, d224272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d222655 q = 0) : d224273 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222655, d224273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222655, d224273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d222656 q = 0) : d224274 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222656, d224274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222656, d224274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d222725 q = 0) : d224343 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222725, d224343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222725, d224343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d222726 q = 0) : d224344 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222726, d224344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d222726, d224344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro21905 (p : Pattern) (selected : d222732 p = 0) : d224350 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222727 q = 0) : d224345 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222727, d224345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21904 q selected
    | true =>
      simp only [d222727, d224345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222728 q = 0) : d224346 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222728, d224346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222728, d224346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222660 q = 0) : d224278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21889 q selected
    | true =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222661 q = 0) : d224279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222729 q = 0) : d224347 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222729, d224347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222729, d224347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222730 q = 0) : d224348 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222730, d224348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222730, d224348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222731 q = 0) : d224349 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222731, d224349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222731, d224349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222732 q = 0) : d224350 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222732, d224350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222732, d224350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21906 (p : Pattern) (selected : d9659 p = 0) : d101071 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9655 q = 0) : d101067 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9655, d101067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6653 q selected
    | true =>
      simp only [d9655, d101067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9656 q = 0) : d101068 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9656, d101068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9656, d101068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9657 q = 0) : d101069 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9657, d101069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9657, d101069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9658 q = 0) : d101070 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9658, d101070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9658, d101070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9659 q = 0) : d101071 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9659, d101071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9659, d101071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro21907 (p : Pattern) (selected : d222740 p = 0) : d224266 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117245 q = 0) : d118831 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117245, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8925 q selected
    | true =>
      simp only [d117245, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117246 q = 0) : d118832 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117246, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117246, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117247 q = 0) : d118833 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117247, d118833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117247, d118833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117248 q = 0) : d118834 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117248, d118834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117248, d118834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222734 q = 0) : d119012 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d222734, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21906 q selected
    | true =>
      simp only [d222734, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222735 q = 0) : d119013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d222735, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222735, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222736 q = 0) : d119014 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d222736, d119014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222736, d119014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222737 q = 0) : d119015 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d222737, d119015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222737, d119015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222738 q = 0) : d224158 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222738, d224158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222738, d224158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222739 q = 0) : d119016 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222739, d119016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222739, d119016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d222740 q = 0) : d224266 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222740, d224266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222740, d224266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21908 (p : Pattern) (selected : d222741 p = 0) : d224267 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117026 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8880 q selected
    | true =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117027 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117028 q = 0) : d118718 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117028, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117028, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117029 q = 0) : d118719 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117029, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117029, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117250 q = 0) : d118943 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117250, d118943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117250, d118943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222741 q = 0) : d224267 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222741, d224267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222741, d224267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21909 (p : Pattern) (selected : d222751 p = 0) : d224277 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222742 q = 0) : d224268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222742, d224268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21907 q selected
    | true =>
      simp only [d222742, d224268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21908 q selected
  have h2 (q : Pattern) (selected : d222743 q = 0) : d224269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222743, d224269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222743, d224269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222744 q = 0) : d224270 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222744, d224270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222744, d224270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222745 q = 0) : d224271 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222745, d224271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21908 q selected
    | true =>
      simp only [d222745, d224271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222746 q = 0) : d224272 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222746, d224272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222746, d224272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222747 q = 0) : d224273 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222747, d224273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222747, d224273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222748 q = 0) : d224274 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222748, d224274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222748, d224274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222749 q = 0) : d224275 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222749, d224275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222749, d224275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222750 q = 0) : d224276 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222750, d224276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222750, d224276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222751 q = 0) : d224277 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222751, d224277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222751, d224277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21910 (p : Pattern) (selected : d222755 p = 0) : d224281 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222745 q = 0) : d224271 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222745, d224271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21908 q selected
    | true =>
      simp only [d222745, d224271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222746 q = 0) : d224272 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222746, d224272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222746, d224272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222747 q = 0) : d224273 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222747, d224273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222747, d224273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222749 q = 0) : d224275 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222749, d224275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222749, d224275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222754 q = 0) : d224280 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222754, d224280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222754, d224280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222755 q = 0) : d224281 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222755, d224281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222755, d224281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21911 (p : Pattern) (selected : d222761 p = 0) : d224287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222752 q = 0) : d224278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222752, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21909 q selected
    | true =>
      simp only [d222752, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222753 q = 0) : d224279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222753, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222753, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222756 q = 0) : d224282 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222756, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21910 q selected
    | true =>
      simp only [d222756, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222757 q = 0) : d224283 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222757, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222757, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222758 q = 0) : d224284 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222758, d224284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222758, d224284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222759 q = 0) : d224285 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222759, d224285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222759, d224285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222760 q = 0) : d224286 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222760, d224286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222760, d224286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222761 q = 0) : d224287 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222761, d224287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222761, d224287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21912 (p : Pattern) (selected : d222765 p = 0) : d224291 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222756 q = 0) : d224282 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222756, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21910 q selected
    | true =>
      simp only [d222756, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222757 q = 0) : d224283 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222757, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222757, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222762 q = 0) : d224288 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222762, d224288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222762, d224288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222763 q = 0) : d224289 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222763, d224289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222763, d224289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222764 q = 0) : d224290 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222764, d224290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222764, d224290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222765 q = 0) : d224291 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222765, d224291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222765, d224291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21913 (p : Pattern) (selected : d222771 p = 0) : d224356 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222660 q = 0) : d224278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21889 q selected
    | true =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222661 q = 0) : d224279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222768 q = 0) : d224353 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222768, d224353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222768, d224353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222769 q = 0) : d224354 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222769, d224354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222769, d224354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222770 q = 0) : d224355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222770, d224355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222770, d224355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222771 q = 0) : d224356 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222771, d224356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222771, d224356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21914 (p : Pattern) (selected : d222777 p = 0) : d224362 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222697 q = 0) : d224315 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222697, d224315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21897 q selected
    | true =>
      simp only [d222697, d224315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21898 q selected
  have h2 (q : Pattern) (selected : d222698 q = 0) : d224316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222698, d224316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222698, d224316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222699 q = 0) : d224317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222699, d224317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222699, d224317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222700 q = 0) : d224318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222700, d224318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222700, d224318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222707 q = 0) : d224325 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222707, d224325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21899 q selected
    | true =>
      simp only [d222707, d224325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21900 q selected
  have h6 (q : Pattern) (selected : d222708 q = 0) : d224326 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222708, d224326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222708, d224326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222709 q = 0) : d224327 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222709, d224327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222709, d224327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222733 q = 0) : d224351 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222733, d224351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21905 q selected
    | true =>
      simp only [d222733, d224351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21891 q selected
  have h9 (q : Pattern) (selected : d222766 q = 0) : d224292 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222766, d224292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21911 q selected
    | true =>
      simp only [d222766, d224292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21912 q selected
  have h10 (q : Pattern) (selected : d222767 q = 0) : d224352 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222767, d224352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222767, d224352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222772 q = 0) : d224357 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222772, d224357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21913 q selected
    | true =>
      simp only [d222772, d224357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d222773 q = 0) : d224358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222773, d224358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d222773, d224358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d222774 q = 0) : d224359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222774, d224359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222774, d224359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d222775 q = 0) : d224360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222775, d224360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222775, d224360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d222776 q = 0) : d224361 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222776, d224361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222776, d224361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d222777 q = 0) : d224362 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222777, d224362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222777, d224362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro21915 (p : Pattern) (selected : d222778 p = 0) : d224363 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222660 q = 0) : d224278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21889 q selected
    | true =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222661 q = 0) : d224279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222664 q = 0) : d224282 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21890 q selected
    | true =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222665 q = 0) : d224283 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222666 q = 0) : d224284 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222666, d224284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222666, d224284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222667 q = 0) : d224285 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222667, d224285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222667, d224285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222693 q = 0) : d224311 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222693, d224311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222693, d224311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222778 q = 0) : d224363 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222778, d224363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222778, d224363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21916 (p : Pattern) (selected : d222779 p = 0) : d224364 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222664 q = 0) : d224282 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21890 q selected
    | true =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222665 q = 0) : d224283 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222670 q = 0) : d224288 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222670, d224288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222670, d224288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222671 q = 0) : d224289 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222671, d224289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222671, d224289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222695 q = 0) : d224313 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222695, d224313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222695, d224313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222779 q = 0) : d224364 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222779, d224364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222779, d224364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21917 (p : Pattern) (selected : d222784 p = 0) : d224369 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222660 q = 0) : d224278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21889 q selected
    | true =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222661 q = 0) : d224279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222664 q = 0) : d224282 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21890 q selected
    | true =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222665 q = 0) : d224283 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222666 q = 0) : d224284 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222666, d224284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222666, d224284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222701 q = 0) : d224319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222701, d224319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222701, d224319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222702 q = 0) : d224320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222702, d224320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222702, d224320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222784 q = 0) : d224369 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222784, d224369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222784, d224369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21918 (p : Pattern) (selected : d222785 p = 0) : d224370 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222664 q = 0) : d224282 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21890 q selected
    | true =>
      simp only [d222664, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222665 q = 0) : d224283 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222665, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222670 q = 0) : d224288 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222670, d224288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222670, d224288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222704 q = 0) : d224322 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222704, d224322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222704, d224322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222705 q = 0) : d224323 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222705, d224323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222705, d224323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222785 q = 0) : d224370 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222785, d224370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222785, d224370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21919 (p : Pattern) (selected : d222789 p = 0) : d224374 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222727 q = 0) : d224345 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222727, d224345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21904 q selected
    | true =>
      simp only [d222727, d224345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222728 q = 0) : d224346 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222728, d224346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222728, d224346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222660 q = 0) : d224278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21889 q selected
    | true =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222661 q = 0) : d224279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222729 q = 0) : d224347 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222729, d224347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222729, d224347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222730 q = 0) : d224348 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222730, d224348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222730, d224348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222731 q = 0) : d224349 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222731, d224349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222731, d224349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222789 q = 0) : d224374 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222789, d224374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222789, d224374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21920 (p : Pattern) (selected : d222791 p = 0) : d224300 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222752 q = 0) : d224278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222752, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21909 q selected
    | true =>
      simp only [d222752, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222753 q = 0) : d224279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222753, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222753, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222756 q = 0) : d224282 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222756, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21910 q selected
    | true =>
      simp only [d222756, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222757 q = 0) : d224283 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222757, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222757, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222758 q = 0) : d224284 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222758, d224284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222758, d224284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222759 q = 0) : d224285 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222759, d224285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222759, d224285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222760 q = 0) : d224286 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222760, d224286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222760, d224286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222791 q = 0) : d224300 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222791, d224300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222791, d224300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21921 (p : Pattern) (selected : d222792 p = 0) : d224301 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222756 q = 0) : d224282 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222756, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21910 q selected
    | true =>
      simp only [d222756, d224282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222757 q = 0) : d224283 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222757, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222757, d224283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222762 q = 0) : d224288 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222762, d224288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222762, d224288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222763 q = 0) : d224289 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222763, d224289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222763, d224289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222764 q = 0) : d224290 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222764, d224290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222764, d224290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222792 q = 0) : d224301 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222792, d224301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222792, d224301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21922 (p : Pattern) (selected : d222795 p = 0) : d224377 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222660 q = 0) : d224278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21889 q selected
    | true =>
      simp only [d222660, d224278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222661 q = 0) : d224279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222661, d224279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222768 q = 0) : d224353 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222768, d224353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222768, d224353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222769 q = 0) : d224354 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222769, d224354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222769, d224354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222770 q = 0) : d224355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222770, d224355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222770, d224355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222795 q = 0) : d224377 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222795, d224377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222795, d224377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21923 (p : Pattern) (selected : d222801 p = 0) : d224383 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222697 q = 0) : d224315 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222697, d224315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21897 q selected
    | true =>
      simp only [d222697, d224315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21898 q selected
  have h2 (q : Pattern) (selected : d222698 q = 0) : d224316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222698, d224316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222698, d224316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222699 q = 0) : d224317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222699, d224317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222699, d224317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222700 q = 0) : d224318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222700, d224318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222700, d224318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222707 q = 0) : d224325 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222707, d224325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21899 q selected
    | true =>
      simp only [d222707, d224325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21900 q selected
  have h6 (q : Pattern) (selected : d222708 q = 0) : d224326 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222708, d224326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222708, d224326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222709 q = 0) : d224327 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222709, d224327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222709, d224327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222733 q = 0) : d224351 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222733, d224351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21905 q selected
    | true =>
      simp only [d222733, d224351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21891 q selected
  have h9 (q : Pattern) (selected : d222766 q = 0) : d224292 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222766, d224292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21911 q selected
    | true =>
      simp only [d222766, d224292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21912 q selected
  have h10 (q : Pattern) (selected : d222767 q = 0) : d224352 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222767, d224352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222767, d224352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222772 q = 0) : d224357 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222772, d224357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21913 q selected
    | true =>
      simp only [d222772, d224357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d222773 q = 0) : d224358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222773, d224358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d222773, d224358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d222774 q = 0) : d224359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222774, d224359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222774, d224359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d222775 q = 0) : d224360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222775, d224360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222775, d224360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d222776 q = 0) : d224361 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222776, d224361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222776, d224361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d222780 q = 0) : d224365 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222780, d224365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21915 q selected
    | true =>
      simp only [d222780, d224365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21916 q selected
  have h17 (q : Pattern) (selected : d222781 q = 0) : d224366 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222781, d224366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222781, d224366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d222782 q = 0) : d224367 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222782, d224367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d222782, d224367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d222783 q = 0) : d224368 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222783, d224368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222783, d224368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d222786 q = 0) : d224371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222786, d224371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21917 q selected
    | true =>
      simp only [d222786, d224371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21918 q selected
  have h21 (q : Pattern) (selected : d222787 q = 0) : d224372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222787, d224372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222787, d224372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d222788 q = 0) : d224373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222788, d224373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d222788, d224373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d222790 q = 0) : d224375 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222790, d224375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21919 q selected
    | true =>
      simp only [d222790, d224375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21894 q selected
  have h24 (q : Pattern) (selected : d222793 q = 0) : d224302 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222793, d224302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21920 q selected
    | true =>
      simp only [d222793, d224302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21921 q selected
  have h25 (q : Pattern) (selected : d222794 q = 0) : d224376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222794, d224376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d222794, d224376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d222796 q = 0) : d224378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222796, d224378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21922 q selected
    | true =>
      simp only [d222796, d224378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d222797 q = 0) : d224379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222797, d224379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d222797, d224379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d222798 q = 0) : d224380 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222798, d224380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d222798, d224380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d222799 q = 0) : d224381 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222799, d224381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d222799, d224381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d222800 q = 0) : d224382 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222800, d224382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d222800, d224382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d222801 q = 0) : d224383 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222801, d224383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d222801, d224383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro21924 (p : Pattern) (selected : d222808 p = 0) : d224390 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222674 q = 0) : d224292 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222674, d224292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21891 q selected
    | true =>
      simp only [d222674, d224292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21892 q selected
  have h2 (q : Pattern) (selected : d222675 q = 0) : d224293 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222675, d224293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222675, d224293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222676 q = 0) : d224294 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222676, d224294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222676, d224294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222677 q = 0) : d224295 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222677, d224295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222677, d224295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222678 q = 0) : d224296 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222678, d224296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222678, d224296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222803 q = 0) : d224385 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222803, d224385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21892 q selected
    | true =>
      simp only [d222803, d224385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222804 q = 0) : d224386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222804, d224386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222804, d224386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222805 q = 0) : d224387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222805, d224387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222805, d224387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222806 q = 0) : d224388 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222806, d224388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222806, d224388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222807 q = 0) : d224389 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222807, d224389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222807, d224389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222808 q = 0) : d224390 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222808, d224390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222808, d224390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21925 (p : Pattern) (selected : d222814 p = 0) : d224396 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222803 q = 0) : d224385 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222803, d224385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21892 q selected
    | true =>
      simp only [d222803, d224385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222804 q = 0) : d224386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222804, d224386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222804, d224386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222805 q = 0) : d224387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222805, d224387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222805, d224387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222806 q = 0) : d224388 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222806, d224388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222806, d224388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222807 q = 0) : d224389 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222807, d224389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222807, d224389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222809 q = 0) : d224391 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222809, d224391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21895 q selected
    | true =>
      simp only [d222809, d224391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222810 q = 0) : d224392 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222810, d224392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222810, d224392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222811 q = 0) : d224393 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222811, d224393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222811, d224393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222812 q = 0) : d224394 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222812, d224394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222812, d224394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222813 q = 0) : d224395 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222813, d224395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222813, d224395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222814 q = 0) : d224396 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222814, d224396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222814, d224396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21926 (p : Pattern) (selected : d222821 p = 0) : d224403 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222790 q = 0) : d224375 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222790, d224375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21919 q selected
    | true =>
      simp only [d222790, d224375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21894 q selected
  have h2 (q : Pattern) (selected : d222793 q = 0) : d224302 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222793, d224302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21920 q selected
    | true =>
      simp only [d222793, d224302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21921 q selected
  have h3 (q : Pattern) (selected : d222794 q = 0) : d224376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222794, d224376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222794, d224376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222796 q = 0) : d224378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222796, d224378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21922 q selected
    | true =>
      simp only [d222796, d224378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222797 q = 0) : d224379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222797, d224379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222797, d224379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222798 q = 0) : d224380 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222798, d224380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222798, d224380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222819 q = 0) : d224401 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222819, d224401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222819, d224401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222820 q = 0) : d224402 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222820, d224402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222820, d224402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d222821 q = 0) : d224403 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222821, d224403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222821, d224403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21927 (p : Pattern) (selected : d222823 p = 0) : d224405 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222809 q = 0) : d224391 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222809, d224391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21895 q selected
    | true =>
      simp only [d222809, d224391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222810 q = 0) : d224392 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222810, d224392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222810, d224392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222811 q = 0) : d224393 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222811, d224393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222811, d224393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222812 q = 0) : d224394 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222812, d224394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222812, d224394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222813 q = 0) : d224395 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222813, d224395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222813, d224395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222823 q = 0) : d224405 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222823, d224405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222823, d224405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21928 (p : Pattern) (selected : d222835 p = 0) : d224417 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117338 q = 0) : d119089 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117338, d119089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117338, d119089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8919 q selected
  have h2 (q : Pattern) (selected : d117219 q = 0) : d119004 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117219, d119004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8919 q selected
    | true =>
      simp only [d117219, d119004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117339 q = 0) : d119090 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117339, d119090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117339, d119090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117220 q = 0) : d119005 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117220, d119005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117220, d119005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117340 q = 0) : d119091 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117340, d119091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117340, d119091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117341 q = 0) : d119092 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117341, d119092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117341, d119092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222829 q = 0) : d224411 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d222829, d224411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222829, d224411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21901 q selected
  have h8 (q : Pattern) (selected : d222710 q = 0) : d224328 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d222710, d224328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21901 q selected
    | true =>
      simp only [d222710, d224328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222830 q = 0) : d224412 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d222830, d224412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222830, d224412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222711 q = 0) : d224329 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d222711, d224329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222711, d224329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d222831 q = 0) : d224413 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d222831, d224413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222831, d224413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d222832 q = 0) : d224414 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d222832, d224414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d222832, d224414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d222833 q = 0) : d224415 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222833, d224415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222833, d224415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117346 q = 0) : d119097 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117346, d119097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117346, d119097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8921 q selected
  have h15 (q : Pattern) (selected : d117227 q = 0) : d119012 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8921 q selected
    | true =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d117347 q = 0) : d119098 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117347, d119098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d117347, d119098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d117228 q = 0) : d119013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d117348 q = 0) : d119099 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117348, d119099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d117348, d119099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d117349 q = 0) : d119100 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117349, d119100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d117349, d119100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d222834 q = 0) : d224416 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222834, d224416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d222834, d224416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d222835 q = 0) : d224417 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222835, d224417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d222835, d224417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro21929 (p : Pattern) (selected : d222836 p = 0) : d224418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117092 q = 0) : d118895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117092, d118895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117092, d118895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8876 q selected
  have h2 (q : Pattern) (selected : d117008 q = 0) : d118831 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117008, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8876 q selected
    | true =>
      simp only [d117008, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117093 q = 0) : d118896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117093, d118896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117093, d118896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117009 q = 0) : d118832 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117009, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117009, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117094 q = 0) : d118897 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117094, d118897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117094, d118897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117095 q = 0) : d118898 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117095, d118898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117095, d118898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117346 q = 0) : d119097 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117346, d119097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117346, d119097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8921 q selected
  have h8 (q : Pattern) (selected : d117227 q = 0) : d119012 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8921 q selected
    | true =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117347 q = 0) : d119098 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117347, d119098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117347, d119098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117228 q = 0) : d119013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117348 q = 0) : d119099 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117348, d119099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117348, d119099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117349 q = 0) : d119100 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117349, d119100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117349, d119100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d222588 q = 0) : d224220 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222588, d224220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222588, d224220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117350 q = 0) : d119101 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117350, d119101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117350, d119101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d222836 q = 0) : d224418 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222836, d224418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d222836, d224418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21930 (p : Pattern) (selected : d222840 p = 0) : d224422 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117346 q = 0) : d119097 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117346, d119097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117346, d119097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8921 q selected
  have h2 (q : Pattern) (selected : d117227 q = 0) : d119012 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8921 q selected
    | true =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117347 q = 0) : d119098 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117347, d119098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117347, d119098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117228 q = 0) : d119013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117348 q = 0) : d119099 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117348, d119099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117348, d119099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117349 q = 0) : d119100 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117349, d119100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117349, d119100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117350 q = 0) : d119101 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117350, d119101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117350, d119101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222840 q = 0) : d224422 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222840, d224422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222840, d224422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21931 (p : Pattern) (selected : d222845 p = 0) : d224427 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116928 q = 0) : d118769 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116928, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116928, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8847 q selected
  have h2 (q : Pattern) (selected : d116855 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8847 q selected
    | true =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116929 q = 0) : d118770 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116929, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116929, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116856 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116930 q = 0) : d118771 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116930, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116930, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116931 q = 0) : d118772 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116931, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116931, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117355 q = 0) : d119106 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117355, d119106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117355, d119106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222845 q = 0) : d224427 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222845, d224427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222845, d224427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21932 (p : Pattern) (selected : d222854 p = 0) : d224436 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222837 q = 0) : d224419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222837, d224419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21928 q selected
    | true =>
      simp only [d222837, d224419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21929 q selected
  have h2 (q : Pattern) (selected : d222838 q = 0) : d224420 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222838, d224420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222838, d224420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222839 q = 0) : d224421 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222839, d224421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222839, d224421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222841 q = 0) : d224423 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222841, d224423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21929 q selected
    | true =>
      simp only [d222841, d224423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21930 q selected
  have h5 (q : Pattern) (selected : d222842 q = 0) : d224424 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222842, d224424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222842, d224424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222843 q = 0) : d224425 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222843, d224425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222843, d224425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222844 q = 0) : d224426 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222844, d224426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222844, d224426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222846 q = 0) : d224428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222846, d224428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21929 q selected
    | true =>
      simp only [d222846, d224428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21931 q selected
  have h9 (q : Pattern) (selected : d222847 q = 0) : d224429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222847, d224429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222847, d224429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222848 q = 0) : d224430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222848, d224430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222848, d224430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222849 q = 0) : d224431 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222849, d224431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21931 q selected
    | true =>
      simp only [d222849, d224431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d222850 q = 0) : d224432 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222850, d224432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222850, d224432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d222851 q = 0) : d224433 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222851, d224433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222851, d224433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d222852 q = 0) : d224434 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222852, d224434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222852, d224434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d222853 q = 0) : d224435 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222853, d224435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222853, d224435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d222854 q = 0) : d224436 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222854, d224436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d222854, d224436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro21933 (p : Pattern) (selected : d222859 p = 0) : d224441 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222846 q = 0) : d224428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222846, d224428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21929 q selected
    | true =>
      simp only [d222846, d224428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21931 q selected
  have h2 (q : Pattern) (selected : d222847 q = 0) : d224429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222847, d224429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222847, d224429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222848 q = 0) : d224430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222848, d224430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222848, d224430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222849 q = 0) : d224431 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222849, d224431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21931 q selected
    | true =>
      simp only [d222849, d224431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222850 q = 0) : d224432 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222850, d224432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222850, d224432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222851 q = 0) : d224433 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222851, d224433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222851, d224433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222852 q = 0) : d224434 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222852, d224434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222852, d224434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222857 q = 0) : d224439 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222857, d224439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222857, d224439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222858 q = 0) : d224440 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222858, d224440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222858, d224440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222859 q = 0) : d224441 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222859, d224441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222859, d224441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21934 (p : Pattern) (selected : d222865 p = 0) : d224447 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222855 q = 0) : d224437 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222855, d224437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21932 q selected
    | true =>
      simp only [d222855, d224437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222856 q = 0) : d224438 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222856, d224438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222856, d224438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222860 q = 0) : d224442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222860, d224442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21933 q selected
    | true =>
      simp only [d222860, d224442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222861 q = 0) : d224443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222861, d224443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222861, d224443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222862 q = 0) : d224444 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222862, d224444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222862, d224444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222863 q = 0) : d224445 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222863, d224445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222863, d224445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222864 q = 0) : d224446 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222864, d224446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222864, d224446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222865 q = 0) : d224447 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222865, d224447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222865, d224447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21935 (p : Pattern) (selected : d222867 p = 0) : d224449 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222849 q = 0) : d224431 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222849, d224431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21931 q selected
    | true =>
      simp only [d222849, d224431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222850 q = 0) : d224432 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222850, d224432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222850, d224432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222851 q = 0) : d224433 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222851, d224433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222851, d224433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222857 q = 0) : d224439 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222857, d224439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222857, d224439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222866 q = 0) : d224448 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222866, d224448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222866, d224448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222867 q = 0) : d224449 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222867, d224449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222867, d224449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21936 (p : Pattern) (selected : d222873 p = 0) : d224455 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222860 q = 0) : d224442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222860, d224442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21933 q selected
    | true =>
      simp only [d222860, d224442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222861 q = 0) : d224443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222861, d224443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222861, d224443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222868 q = 0) : d224450 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222868, d224450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21935 q selected
    | true =>
      simp only [d222868, d224450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222869 q = 0) : d224451 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222869, d224451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222869, d224451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222870 q = 0) : d224452 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222870, d224452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222870, d224452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222871 q = 0) : d224453 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222871, d224453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222871, d224453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222872 q = 0) : d224454 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222872, d224454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222872, d224454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222873 q = 0) : d224455 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222873, d224455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222873, d224455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21937 (p : Pattern) (selected : d222881 p = 0) : d224418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117385 q = 0) : d118895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117385, d118895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117385, d118895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8925 q selected
  have h2 (q : Pattern) (selected : d117245 q = 0) : d118831 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117245, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8925 q selected
    | true =>
      simp only [d117245, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117386 q = 0) : d118896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117386, d118896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117386, d118896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117246 q = 0) : d118832 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117246, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117246, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117387 q = 0) : d118897 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117387, d118897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117387, d118897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117388 q = 0) : d118898 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117388, d118898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117388, d118898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222875 q = 0) : d119097 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d222875, d119097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222875, d119097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21906 q selected
  have h8 (q : Pattern) (selected : d222734 q = 0) : d119012 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d222734, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21906 q selected
    | true =>
      simp only [d222734, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222876 q = 0) : d119098 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d222876, d119098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222876, d119098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222735 q = 0) : d119013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d222735, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222735, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d222877 q = 0) : d119099 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d222877, d119099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222877, d119099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d222878 q = 0) : d119100 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d222878, d119100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d222878, d119100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d222879 q = 0) : d224220 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222879, d224220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222879, d224220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d222880 q = 0) : d119101 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222880, d119101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d222880, d119101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d222881 q = 0) : d224418 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222881, d224418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d222881, d224418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21938 (p : Pattern) (selected : d222882 p = 0) : d224427 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117110 q = 0) : d118769 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117110, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117110, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8880 q selected
  have h2 (q : Pattern) (selected : d117026 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8880 q selected
    | true =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117111 q = 0) : d118770 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117111, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117111, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117027 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117112 q = 0) : d118771 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117112, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117112, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117113 q = 0) : d118772 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117113, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117113, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117390 q = 0) : d119106 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117390, d119106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117390, d119106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222882 q = 0) : d224427 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222882, d224427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222882, d224427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21939 (p : Pattern) (selected : d222892 p = 0) : d224441 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222883 q = 0) : d224428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222883, d224428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21937 q selected
    | true =>
      simp only [d222883, d224428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21938 q selected
  have h2 (q : Pattern) (selected : d222884 q = 0) : d224429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222884, d224429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222884, d224429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222885 q = 0) : d224430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222885, d224430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222885, d224430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222886 q = 0) : d224431 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222886, d224431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21938 q selected
    | true =>
      simp only [d222886, d224431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222887 q = 0) : d224432 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222887, d224432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222887, d224432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222888 q = 0) : d224433 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222888, d224433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222888, d224433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222889 q = 0) : d224434 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222889, d224434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222889, d224434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222890 q = 0) : d224439 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222890, d224439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222890, d224439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222891 q = 0) : d224440 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222891, d224440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222891, d224440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222892 q = 0) : d224441 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222892, d224441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222892, d224441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21940 (p : Pattern) (selected : d222896 p = 0) : d224449 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222886 q = 0) : d224431 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222886, d224431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21938 q selected
    | true =>
      simp only [d222886, d224431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222887 q = 0) : d224432 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222887, d224432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222887, d224432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222888 q = 0) : d224433 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222888, d224433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222888, d224433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222890 q = 0) : d224439 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222890, d224439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222890, d224439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222895 q = 0) : d224448 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222895, d224448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222895, d224448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222896 q = 0) : d224449 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222896, d224449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222896, d224449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21941 (p : Pattern) (selected : d222902 p = 0) : d224455 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222893 q = 0) : d224442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222893, d224442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21939 q selected
    | true =>
      simp only [d222893, d224442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222894 q = 0) : d224443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222894, d224443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222894, d224443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222897 q = 0) : d224450 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222897, d224450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21940 q selected
    | true =>
      simp only [d222897, d224450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222898 q = 0) : d224451 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222898, d224451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222898, d224451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222899 q = 0) : d224452 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222899, d224452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222899, d224452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222900 q = 0) : d224453 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222900, d224453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222900, d224453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222901 q = 0) : d224454 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222901, d224454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222901, d224454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222902 q = 0) : d224455 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222902, d224455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222902, d224455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21942 (p : Pattern) (selected : d222906 p = 0) : d224460 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222897 q = 0) : d224450 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222897, d224450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21940 q selected
    | true =>
      simp only [d222897, d224450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222898 q = 0) : d224451 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222898, d224451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222898, d224451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222903 q = 0) : d224457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222903, d224457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222903, d224457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222904 q = 0) : d224458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222904, d224458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222904, d224458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222905 q = 0) : d224459 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222905, d224459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222905, d224459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222906 q = 0) : d224460 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222906, d224460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222906, d224460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21943 (p : Pattern) (selected : d222912 p = 0) : d224466 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222860 q = 0) : d224442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222860, d224442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21933 q selected
    | true =>
      simp only [d222860, d224442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222861 q = 0) : d224443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222861, d224443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222861, d224443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222909 q = 0) : d224463 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222909, d224463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222909, d224463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222910 q = 0) : d224464 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222910, d224464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222910, d224464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222911 q = 0) : d224465 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222911, d224465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222911, d224465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222912 q = 0) : d224466 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222912, d224466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222912, d224466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21944 (p : Pattern) (selected : d222918 p = 0) : d224472 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222874 q = 0) : d224456 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222874, d224456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21934 q selected
    | true =>
      simp only [d222874, d224456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21936 q selected
  have h2 (q : Pattern) (selected : d222907 q = 0) : d224461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222907, d224461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21941 q selected
    | true =>
      simp only [d222907, d224461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21942 q selected
  have h3 (q : Pattern) (selected : d222908 q = 0) : d224462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222908, d224462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222908, d224462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222913 q = 0) : d224467 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222913, d224467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21943 q selected
    | true =>
      simp only [d222913, d224467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222914 q = 0) : d224468 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222914, d224468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222914, d224468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222915 q = 0) : d224469 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222915, d224469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222915, d224469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222916 q = 0) : d224470 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222916, d224470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222916, d224470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222917 q = 0) : d224471 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222917, d224471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222917, d224471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d222918 q = 0) : d224472 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222918, d224472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222918, d224472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21945 (p : Pattern) (selected : d222923 p = 0) : d224460 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222868 q = 0) : d224450 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222868, d224450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21935 q selected
    | true =>
      simp only [d222868, d224450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222869 q = 0) : d224451 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222869, d224451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222869, d224451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222920 q = 0) : d224457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222920, d224457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222920, d224457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222921 q = 0) : d224458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222921, d224458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222921, d224458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222922 q = 0) : d224459 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222922, d224459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222922, d224459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222923 q = 0) : d224460 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222923, d224460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222923, d224460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21946 (p : Pattern) (selected : d222929 p = 0) : d224479 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222924 q = 0) : d224474 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222924, d224474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21945 q selected
    | true =>
      simp only [d222924, d224474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222925 q = 0) : d224475 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222925, d224475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222925, d224475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222926 q = 0) : d224476 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222926, d224476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222926, d224476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222927 q = 0) : d224477 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222927, d224477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222927, d224477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222928 q = 0) : d224478 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222928, d224478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222928, d224478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222929 q = 0) : d224479 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222929, d224479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222929, d224479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21947 (p : Pattern) (selected : d222935 p = 0) : d224485 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222680 q = 0) : d224298 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222680, d224298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222680, d224298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21893 q selected
  have h2 (q : Pattern) (selected : d222681 q = 0) : d224299 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222681, d224299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222681, d224299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d222690 q = 0) : d224308 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222690, d224308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21893 q selected
    | true =>
      simp only [d222690, d224308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21896 q selected
  have h4 (q : Pattern) (selected : d222691 q = 0) : d224309 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222691, d224309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222691, d224309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222692 q = 0) : d224310 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222692, d224310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222692, d224310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222802 q = 0) : d224384 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222802, d224384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21914 q selected
    | true =>
      simp only [d222802, d224384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21923 q selected
  have h7 (q : Pattern) (selected : d222815 q = 0) : d224397 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222815, d224397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21924 q selected
    | true =>
      simp only [d222815, d224397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21925 q selected
  have h8 (q : Pattern) (selected : d222816 q = 0) : d224398 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222816, d224398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222816, d224398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d222817 q = 0) : d224399 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222817, d224399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222817, d224399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d222818 q = 0) : d224400 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222818, d224400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222818, d224400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222822 q = 0) : d224404 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222822, d224404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222822, d224404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21926 q selected
  have h12 (q : Pattern) (selected : d222824 q = 0) : d224406 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222824, d224406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222824, d224406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21927 q selected
  have h13 (q : Pattern) (selected : d222825 q = 0) : d224407 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222825, d224407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d222825, d224407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d222826 q = 0) : d224408 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222826, d224408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d222826, d224408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d222827 q = 0) : d224409 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222827, d224409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d222827, d224409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d222828 q = 0) : d224410 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d222828, d224410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222828, d224410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d222919 q = 0) : d224473 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222919, d224473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222919, d224473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21944 q selected
  have h18 (q : Pattern) (selected : d222930 q = 0) : d224480 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222930, d224480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222930, d224480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21946 q selected
  have h19 (q : Pattern) (selected : d222931 q = 0) : d224481 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222931, d224481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d222931, d224481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d222932 q = 0) : d224482 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222932, d224482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d222932, d224482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d222933 q = 0) : d224483 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222933, d224483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d222933, d224483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d222934 q = 0) : d224484 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d222934, d224484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d222934, d224484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d222935 q = 0) : d224485 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d222935, d224485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d222935, d224485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro21948 (p : Pattern) (selected : d222941 p = 0) : d224491 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222936 q = 0) : d224486 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d222936, d224486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222936, d224486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21947 q selected
  have h2 (q : Pattern) (selected : d222937 q = 0) : d224487 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d222937, d224487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222937, d224487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222938 q = 0) : d224488 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d222938, d224488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222938, d224488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222939 q = 0) : d224489 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d222939, d224489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222939, d224489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222940 q = 0) : d224490 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d222940, d224490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222940, d224490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222941 q = 0) : d224491 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d222941, d224491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222941, d224491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21949 (p : Pattern) (selected : d222946 p = 0) : d224496 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117452 q = 0) : d119173 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117452, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8967 q selected
    | true =>
      simp only [d117452, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117453 q = 0) : d119174 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117453, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117453, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117454 q = 0) : d119175 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117454, d119175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117454, d119175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117455 q = 0) : d119176 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117455, d119176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117455, d119176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117535 q = 0) : d119256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117535, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8987 q selected
    | true =>
      simp only [d117535, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117536 q = 0) : d119257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117536, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117536, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117537 q = 0) : d119258 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117537, d119258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117537, d119258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117538 q = 0) : d119259 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117538, d119259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117538, d119259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222944 q = 0) : d224494 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222944, d224494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222944, d224494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117461 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8970 q selected
    | true =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117462 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117463 q = 0) : d119184 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117463, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117463, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117464 q = 0) : d119185 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117464, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117464, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d222945 q = 0) : d224495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222945, d224495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222945, d224495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d222946 q = 0) : d224496 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222946, d224496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222946, d224496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21950 (p : Pattern) (selected : d222947 p = 0) : d224497 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117456 q = 0) : d119177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117456, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8968 q selected
    | true =>
      simp only [d117456, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117457 q = 0) : d119178 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117457, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117457, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117458 q = 0) : d119179 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117458, d119179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117458, d119179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117459 q = 0) : d119180 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117459, d119180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117459, d119180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117461 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8970 q selected
    | true =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117462 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117463 q = 0) : d119184 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117463, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117463, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117464 q = 0) : d119185 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117464, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117464, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117465 q = 0) : d119186 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117465, d119186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117465, d119186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117469 q = 0) : d119190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117469, d119190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117469, d119190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d222947 q = 0) : d224497 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222947, d224497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222947, d224497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21951 (p : Pattern) (selected : d222951 p = 0) : d224501 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117461 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8970 q selected
    | true =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117462 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117463 q = 0) : d119184 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117463, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117463, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117464 q = 0) : d119185 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117464, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117464, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117469 q = 0) : d119190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117469, d119190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117469, d119190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222951 q = 0) : d224501 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222951, d224501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222951, d224501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21952 (p : Pattern) (selected : d222958 p = 0) : d224508 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222948 q = 0) : d224498 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222948, d224498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21949 q selected
    | true =>
      simp only [d222948, d224498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21950 q selected
  have h2 (q : Pattern) (selected : d222949 q = 0) : d224499 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222949, d224499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222949, d224499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222950 q = 0) : d224500 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222950, d224500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222950, d224500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222952 q = 0) : d224502 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222952, d224502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21950 q selected
    | true =>
      simp only [d222952, d224502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21951 q selected
  have h5 (q : Pattern) (selected : d222953 q = 0) : d224503 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222953, d224503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222953, d224503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222954 q = 0) : d224504 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222954, d224504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222954, d224504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222955 q = 0) : d224505 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222955, d224505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222955, d224505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222956 q = 0) : d224506 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222956, d224506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222956, d224506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222957 q = 0) : d224507 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222957, d224507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222957, d224507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222958 q = 0) : d224508 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222958, d224508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222958, d224508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21953 (p : Pattern) (selected : d222962 p = 0) : d224512 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222952 q = 0) : d224502 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222952, d224502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21950 q selected
    | true =>
      simp only [d222952, d224502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21951 q selected
  have h2 (q : Pattern) (selected : d222953 q = 0) : d224503 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222953, d224503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222953, d224503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222954 q = 0) : d224504 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222954, d224504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222954, d224504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222956 q = 0) : d224506 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222956, d224506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222956, d224506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222961 q = 0) : d224511 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222961, d224511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222961, d224511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222962 q = 0) : d224512 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222962, d224512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222962, d224512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21954 (p : Pattern) (selected : d222968 p = 0) : d224518 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222959 q = 0) : d224509 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21952 q selected
    | true =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222960 q = 0) : d224510 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222963 q = 0) : d224513 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21953 q selected
    | true =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222964 q = 0) : d224514 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222965 q = 0) : d224515 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222965, d224515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222965, d224515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222966 q = 0) : d224516 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222966, d224516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222966, d224516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222967 q = 0) : d224517 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222967, d224517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222967, d224517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222968 q = 0) : d224518 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222968, d224518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222968, d224518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21955 (p : Pattern) (selected : d222972 p = 0) : d224522 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222963 q = 0) : d224513 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21953 q selected
    | true =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222964 q = 0) : d224514 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222969 q = 0) : d224519 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222969, d224519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222969, d224519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222970 q = 0) : d224520 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222970, d224520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222970, d224520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222971 q = 0) : d224521 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222971, d224521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222971, d224521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222972 q = 0) : d224522 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222972, d224522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222972, d224522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21956 (p : Pattern) (selected : d222978 p = 0) : d224528 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222973 q = 0) : d224523 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222973, d224523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21954 q selected
    | true =>
      simp only [d222973, d224523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21955 q selected
  have h2 (q : Pattern) (selected : d222974 q = 0) : d224524 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222974, d224524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222974, d224524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222975 q = 0) : d224525 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222975, d224525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222975, d224525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222976 q = 0) : d224526 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222976, d224526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222976, d224526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222977 q = 0) : d224527 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222977, d224527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222977, d224527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222978 q = 0) : d224528 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222978, d224528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222978, d224528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21957 (p : Pattern) (selected : d222981 p = 0) : d224531 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222959 q = 0) : d224509 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21952 q selected
    | true =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222960 q = 0) : d224510 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222963 q = 0) : d224513 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21953 q selected
    | true =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222964 q = 0) : d224514 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222965 q = 0) : d224515 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222965, d224515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222965, d224515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222966 q = 0) : d224516 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222966, d224516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222966, d224516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222967 q = 0) : d224517 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222967, d224517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222967, d224517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222981 q = 0) : d224531 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222981, d224531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222981, d224531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21958 (p : Pattern) (selected : d222982 p = 0) : d224532 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222963 q = 0) : d224513 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21953 q selected
    | true =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222964 q = 0) : d224514 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222969 q = 0) : d224519 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222969, d224519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222969, d224519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222970 q = 0) : d224520 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222970, d224520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222970, d224520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222971 q = 0) : d224521 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222971, d224521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222971, d224521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222982 q = 0) : d224532 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222982, d224532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222982, d224532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21959 (p : Pattern) (selected : d222988 p = 0) : d224538 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222973 q = 0) : d224523 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222973, d224523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21954 q selected
    | true =>
      simp only [d222973, d224523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21955 q selected
  have h2 (q : Pattern) (selected : d222974 q = 0) : d224524 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222974, d224524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222974, d224524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222975 q = 0) : d224525 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222975, d224525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222975, d224525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222976 q = 0) : d224526 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222976, d224526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222976, d224526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222977 q = 0) : d224527 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222977, d224527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222977, d224527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222983 q = 0) : d224533 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222983, d224533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21957 q selected
    | true =>
      simp only [d222983, d224533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21958 q selected
  have h7 (q : Pattern) (selected : d222984 q = 0) : d224534 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222984, d224534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222984, d224534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222985 q = 0) : d224535 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222985, d224535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222985, d224535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222986 q = 0) : d224536 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222986, d224536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222986, d224536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222987 q = 0) : d224537 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222987, d224537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222987, d224537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222988 q = 0) : d224538 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222988, d224538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222988, d224538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21960 (p : Pattern) (selected : d222993 p = 0) : d224543 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222959 q = 0) : d224509 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21952 q selected
    | true =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222960 q = 0) : d224510 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222963 q = 0) : d224513 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21953 q selected
    | true =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222964 q = 0) : d224514 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222965 q = 0) : d224515 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222965, d224515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222965, d224515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222966 q = 0) : d224516 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222966, d224516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222966, d224516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222992 q = 0) : d224542 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222992, d224542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222992, d224542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222993 q = 0) : d224543 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222993, d224543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222993, d224543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21961 (p : Pattern) (selected : d222995 p = 0) : d224545 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222963 q = 0) : d224513 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21953 q selected
    | true =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222964 q = 0) : d224514 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222969 q = 0) : d224519 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222969, d224519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222969, d224519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222970 q = 0) : d224520 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222970, d224520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222970, d224520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222994 q = 0) : d224544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222994, d224544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222994, d224544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222995 q = 0) : d224545 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222995, d224545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222995, d224545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21962 (p : Pattern) (selected : d223002 p = 0) : d224552 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222959 q = 0) : d224509 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21952 q selected
    | true =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222960 q = 0) : d224510 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222963 q = 0) : d224513 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21953 q selected
    | true =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222964 q = 0) : d224514 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222965 q = 0) : d224515 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222965, d224515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222965, d224515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223000 q = 0) : d224550 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223000, d224550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223000, d224550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223001 q = 0) : d224551 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223001, d224551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223001, d224551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223002 q = 0) : d224552 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223002, d224552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223002, d224552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21963 (p : Pattern) (selected : d223005 p = 0) : d224555 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222963 q = 0) : d224513 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21953 q selected
    | true =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222964 q = 0) : d224514 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222969 q = 0) : d224519 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222969, d224519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222969, d224519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223003 q = 0) : d224553 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223003, d224553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223003, d224553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223004 q = 0) : d224554 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223004, d224554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223004, d224554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223005 q = 0) : d224555 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223005, d224555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223005, d224555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21964 (p : Pattern) (selected : d9751 p = 0) : d101272 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9581 q = 0) : d101161 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d101161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6640 q selected
    | true =>
      simp only [d9581, d101161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9582 q = 0) : d101162 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d101162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9582, d101162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9749 q = 0) : d101270 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9749, d101270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9749, d101270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9750 q = 0) : d101271 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9750, d101271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9750, d101271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9751 q = 0) : d101272 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9751, d101272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9751, d101272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro21965 (p : Pattern) (selected : d223015 p = 0) : d224565 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117527 q = 0) : d119248 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117527, d119248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8985 q selected
    | true =>
      simp only [d117527, d119248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117528 q = 0) : d119249 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117528, d119249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117528, d119249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117529 q = 0) : d119250 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117529, d119250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117529, d119250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117530 q = 0) : d119251 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117530, d119251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117530, d119251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223009 q = 0) : d224559 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d223009, d224559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21964 q selected
    | true =>
      simp only [d223009, d224559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223010 q = 0) : d224560 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d223010, d224560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223010, d224560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223011 q = 0) : d224561 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d223011, d224561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223011, d224561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223012 q = 0) : d224562 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d223012, d224562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223012, d224562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223013 q = 0) : d224563 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223013, d224563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223013, d224563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117535 q = 0) : d119256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117535, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8987 q selected
    | true =>
      simp only [d117535, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117536 q = 0) : d119257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117536, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117536, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117537 q = 0) : d119258 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117537, d119258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117537, d119258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117538 q = 0) : d119259 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117538, d119259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117538, d119259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d223014 q = 0) : d224564 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223014, d224564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223014, d224564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223015 q = 0) : d224565 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223015, d224565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223015, d224565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21966 (p : Pattern) (selected : d223019 p = 0) : d224569 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117535 q = 0) : d119256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117535, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8987 q selected
    | true =>
      simp only [d117535, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117536 q = 0) : d119257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117536, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117536, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117537 q = 0) : d119258 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117537, d119258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117537, d119258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117538 q = 0) : d119259 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117538, d119259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117538, d119259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117461 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8970 q selected
    | true =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117462 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117463 q = 0) : d119184 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117463, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117463, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117464 q = 0) : d119185 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117464, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117464, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222945 q = 0) : d224495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222945, d224495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222945, d224495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117469 q = 0) : d119190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117469, d119190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117469, d119190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d223019 q = 0) : d224569 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223019, d224569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223019, d224569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21967 (p : Pattern) (selected : d223025 p = 0) : d224575 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223016 q = 0) : d224566 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223016, d224566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21965 q selected
    | true =>
      simp only [d223016, d224566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21949 q selected
  have h2 (q : Pattern) (selected : d223017 q = 0) : d224567 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223017, d224567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223017, d224567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223018 q = 0) : d224568 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223018, d224568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223018, d224568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223020 q = 0) : d224570 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223020, d224570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21949 q selected
    | true =>
      simp only [d223020, d224570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21966 q selected
  have h5 (q : Pattern) (selected : d223021 q = 0) : d224571 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223021, d224571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223021, d224571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223022 q = 0) : d224572 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223022, d224572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223022, d224572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223023 q = 0) : d224573 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223023, d224573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223023, d224573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222948 q = 0) : d224498 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222948, d224498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21949 q selected
    | true =>
      simp only [d222948, d224498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21950 q selected
  have h9 (q : Pattern) (selected : d222949 q = 0) : d224499 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222949, d224499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222949, d224499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222950 q = 0) : d224500 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222950, d224500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222950, d224500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d222952 q = 0) : d224502 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222952, d224502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21950 q selected
    | true =>
      simp only [d222952, d224502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21951 q selected
  have h12 (q : Pattern) (selected : d222953 q = 0) : d224503 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222953, d224503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222953, d224503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d222954 q = 0) : d224504 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222954, d224504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222954, d224504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d222955 q = 0) : d224505 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222955, d224505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222955, d224505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223024 q = 0) : d224574 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223024, d224574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223024, d224574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223025 q = 0) : d224575 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223025, d224575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d223025, d224575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro21968 (p : Pattern) (selected : d223031 p = 0) : d224581 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223026 q = 0) : d224576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223026, d224576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21967 q selected
    | true =>
      simp only [d223026, d224576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223027 q = 0) : d224577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223027, d224577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223027, d224577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222959 q = 0) : d224509 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21952 q selected
    | true =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222960 q = 0) : d224510 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223028 q = 0) : d224578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223028, d224578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223028, d224578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223029 q = 0) : d224579 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223029, d224579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223029, d224579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223030 q = 0) : d224580 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223030, d224580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223030, d224580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223031 q = 0) : d224581 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223031, d224581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223031, d224581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21969 (p : Pattern) (selected : d9894 p = 0) : d101297 p = 1 := by
  have h0 (q : Pattern) (selected : d9890 q = 0) : d101293 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9890, d101293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6688 q selected
    | true =>
      simp only [d9890, d101293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6689 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d9891 q = 0) : d101294 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9891, d101294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9891, d101294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9655 q = 0) : d101067 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9655, d101067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6653 q selected
    | true =>
      simp only [d9655, d101067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d9656 q = 0) : d101068 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9656, d101068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9656, d101068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d9892 q = 0) : d101295 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9892, d101295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9892, d101295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9893 q = 0) : d101296 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9893, d101296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9893, d101296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d9894 q = 0) : d101297 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9894, d101297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9894, d101297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro21970 (p : Pattern) (selected : d223039 p = 0) : d224496 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117553 q = 0) : d119173 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117553, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8991 q selected
    | true =>
      simp only [d117553, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117554 q = 0) : d119174 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117554, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117554, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117555 q = 0) : d119175 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117555, d119175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117555, d119175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117556 q = 0) : d119176 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117556, d119176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117556, d119176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223033 q = 0) : d119256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d223033, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21969 q selected
    | true =>
      simp only [d223033, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223034 q = 0) : d119257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d223034, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223034, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223035 q = 0) : d119258 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d223035, d119258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223035, d119258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223036 q = 0) : d119259 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d223036, d119259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223036, d119259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223037 q = 0) : d224494 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223037, d224494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223037, d224494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117562 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8994 q selected
    | true =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117563 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117564 q = 0) : d119184 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117564, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117564, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117565 q = 0) : d119185 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117565, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117565, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d223038 q = 0) : d224495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223038, d224495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223038, d224495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223039 q = 0) : d224496 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223039, d224496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223039, d224496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21971 (p : Pattern) (selected : d223040 p = 0) : d224497 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117557 q = 0) : d119177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117557, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8992 q selected
    | true =>
      simp only [d117557, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117558 q = 0) : d119178 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117558, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117558, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117559 q = 0) : d119179 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117559, d119179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117559, d119179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117560 q = 0) : d119180 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117560, d119180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117560, d119180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117562 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8994 q selected
    | true =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117563 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117564 q = 0) : d119184 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117564, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117564, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117565 q = 0) : d119185 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117565, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117565, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117566 q = 0) : d119186 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117566, d119186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117566, d119186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117570 q = 0) : d119190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117570, d119190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117570, d119190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d223040 q = 0) : d224497 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223040, d224497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223040, d224497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21972 (p : Pattern) (selected : d223044 p = 0) : d224501 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117562 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8994 q selected
    | true =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117563 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117564 q = 0) : d119184 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117564, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117564, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117565 q = 0) : d119185 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117565, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117565, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117570 q = 0) : d119190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117570, d119190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117570, d119190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223044 q = 0) : d224501 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223044, d224501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223044, d224501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21973 (p : Pattern) (selected : d223051 p = 0) : d224508 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223041 q = 0) : d224498 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223041, d224498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21970 q selected
    | true =>
      simp only [d223041, d224498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21971 q selected
  have h2 (q : Pattern) (selected : d223042 q = 0) : d224499 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223042, d224499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223042, d224499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223043 q = 0) : d224500 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223043, d224500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223043, d224500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223045 q = 0) : d224502 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223045, d224502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21971 q selected
    | true =>
      simp only [d223045, d224502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21972 q selected
  have h5 (q : Pattern) (selected : d223046 q = 0) : d224503 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223046, d224503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223046, d224503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223047 q = 0) : d224504 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223047, d224504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223047, d224504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223048 q = 0) : d224505 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223048, d224505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223048, d224505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223049 q = 0) : d224506 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223049, d224506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223049, d224506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223050 q = 0) : d224507 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223050, d224507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223050, d224507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223051 q = 0) : d224508 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223051, d224508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223051, d224508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21974 (p : Pattern) (selected : d223055 p = 0) : d224512 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223045 q = 0) : d224502 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223045, d224502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21971 q selected
    | true =>
      simp only [d223045, d224502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21972 q selected
  have h2 (q : Pattern) (selected : d223046 q = 0) : d224503 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223046, d224503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223046, d224503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223047 q = 0) : d224504 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223047, d224504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223047, d224504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223049 q = 0) : d224506 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223049, d224506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223049, d224506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223054 q = 0) : d224511 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223054, d224511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223054, d224511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223055 q = 0) : d224512 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223055, d224512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223055, d224512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21975 (p : Pattern) (selected : d223061 p = 0) : d224518 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223052 q = 0) : d224509 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223052, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21973 q selected
    | true =>
      simp only [d223052, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223053 q = 0) : d224510 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223053, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223053, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223056 q = 0) : d224513 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223056, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21974 q selected
    | true =>
      simp only [d223056, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223057 q = 0) : d224514 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223057, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223057, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223058 q = 0) : d224515 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223058, d224515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223058, d224515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223059 q = 0) : d224516 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223059, d224516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223059, d224516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223060 q = 0) : d224517 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223060, d224517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223060, d224517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223061 q = 0) : d224518 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223061, d224518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223061, d224518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro21976 (p : Pattern) (selected : d223065 p = 0) : d224522 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223056 q = 0) : d224513 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223056, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21974 q selected
    | true =>
      simp only [d223056, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223057 q = 0) : d224514 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223057, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223057, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223062 q = 0) : d224519 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223062, d224519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223062, d224519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223063 q = 0) : d224520 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223063, d224520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223063, d224520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223064 q = 0) : d224521 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223064, d224521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223064, d224521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223065 q = 0) : d224522 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223065, d224522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223065, d224522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21977 (p : Pattern) (selected : d223071 p = 0) : d224587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222959 q = 0) : d224509 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21952 q selected
    | true =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222960 q = 0) : d224510 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223068 q = 0) : d224584 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223068, d224584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223068, d224584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223069 q = 0) : d224585 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223069, d224585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223069, d224585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223070 q = 0) : d224586 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223070, d224586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223070, d224586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223071 q = 0) : d224587 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223071, d224587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223071, d224587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21978 (p : Pattern) (selected : d223077 p = 0) : d224593 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222996 q = 0) : d224546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222996, d224546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21960 q selected
    | true =>
      simp only [d222996, d224546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21961 q selected
  have h2 (q : Pattern) (selected : d222997 q = 0) : d224547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222997, d224547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222997, d224547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222998 q = 0) : d224548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222998, d224548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222998, d224548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222999 q = 0) : d224549 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222999, d224549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222999, d224549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223006 q = 0) : d224556 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223006, d224556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21962 q selected
    | true =>
      simp only [d223006, d224556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21963 q selected
  have h6 (q : Pattern) (selected : d223007 q = 0) : d224557 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223007, d224557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223007, d224557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223008 q = 0) : d224558 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223008, d224558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223008, d224558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223032 q = 0) : d224582 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223032, d224582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21968 q selected
    | true =>
      simp only [d223032, d224582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21954 q selected
  have h9 (q : Pattern) (selected : d223066 q = 0) : d224523 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223066, d224523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21975 q selected
    | true =>
      simp only [d223066, d224523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21976 q selected
  have h10 (q : Pattern) (selected : d223067 q = 0) : d224583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223067, d224583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223067, d224583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223072 q = 0) : d224588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223072, d224588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21977 q selected
    | true =>
      simp only [d223072, d224588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223073 q = 0) : d224589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223073, d224589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d223073, d224589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223074 q = 0) : d224590 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223074, d224590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223074, d224590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d223075 q = 0) : d224591 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223075, d224591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223075, d224591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223076 q = 0) : d224592 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223076, d224592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223076, d224592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223077 q = 0) : d224593 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223077, d224593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223077, d224593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro21979 (p : Pattern) (selected : d223078 p = 0) : d224594 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222959 q = 0) : d224509 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21952 q selected
    | true =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222960 q = 0) : d224510 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222963 q = 0) : d224513 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21953 q selected
    | true =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222964 q = 0) : d224514 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222965 q = 0) : d224515 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222965, d224515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222965, d224515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222966 q = 0) : d224516 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222966, d224516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222966, d224516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222992 q = 0) : d224542 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222992, d224542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222992, d224542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223078 q = 0) : d224594 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223078, d224594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223078, d224594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21980 (p : Pattern) (selected : d223079 p = 0) : d224595 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222963 q = 0) : d224513 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21953 q selected
    | true =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222964 q = 0) : d224514 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222969 q = 0) : d224519 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222969, d224519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222969, d224519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222970 q = 0) : d224520 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222970, d224520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222970, d224520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222994 q = 0) : d224544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222994, d224544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222994, d224544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223079 q = 0) : d224595 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223079, d224595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223079, d224595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21981 (p : Pattern) (selected : d223084 p = 0) : d224600 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222959 q = 0) : d224509 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21952 q selected
    | true =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222960 q = 0) : d224510 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222963 q = 0) : d224513 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21953 q selected
    | true =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222964 q = 0) : d224514 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222965 q = 0) : d224515 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222965, d224515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222965, d224515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223000 q = 0) : d224550 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223000, d224550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223000, d224550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223001 q = 0) : d224551 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223001, d224551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223001, d224551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223084 q = 0) : d224600 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223084, d224600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223084, d224600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21982 (p : Pattern) (selected : d223085 p = 0) : d224601 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222963 q = 0) : d224513 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21953 q selected
    | true =>
      simp only [d222963, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222964 q = 0) : d224514 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222964, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222969 q = 0) : d224519 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222969, d224519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222969, d224519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223003 q = 0) : d224553 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223003, d224553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223003, d224553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223004 q = 0) : d224554 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223004, d224554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223004, d224554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223085 q = 0) : d224601 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223085, d224601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223085, d224601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21983 (p : Pattern) (selected : d223089 p = 0) : d224605 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223026 q = 0) : d224576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223026, d224576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21967 q selected
    | true =>
      simp only [d223026, d224576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223027 q = 0) : d224577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223027, d224577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223027, d224577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222959 q = 0) : d224509 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21952 q selected
    | true =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222960 q = 0) : d224510 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223028 q = 0) : d224578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223028, d224578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223028, d224578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223029 q = 0) : d224579 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223029, d224579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223029, d224579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223030 q = 0) : d224580 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223030, d224580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223030, d224580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223089 q = 0) : d224605 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223089, d224605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223089, d224605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21984 (p : Pattern) (selected : d223091 p = 0) : d224531 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223052 q = 0) : d224509 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223052, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21973 q selected
    | true =>
      simp only [d223052, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223053 q = 0) : d224510 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223053, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223053, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223056 q = 0) : d224513 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223056, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21974 q selected
    | true =>
      simp only [d223056, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223057 q = 0) : d224514 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223057, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223057, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223058 q = 0) : d224515 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223058, d224515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223058, d224515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223059 q = 0) : d224516 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223059, d224516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223059, d224516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223060 q = 0) : d224517 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223060, d224517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223060, d224517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223091 q = 0) : d224531 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223091, d224531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223091, d224531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21985 (p : Pattern) (selected : d223092 p = 0) : d224532 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223056 q = 0) : d224513 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223056, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21974 q selected
    | true =>
      simp only [d223056, d224513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223057 q = 0) : d224514 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223057, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223057, d224514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223062 q = 0) : d224519 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223062, d224519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223062, d224519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223063 q = 0) : d224520 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223063, d224520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223063, d224520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223064 q = 0) : d224521 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223064, d224521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223064, d224521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223092 q = 0) : d224532 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223092, d224532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223092, d224532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21986 (p : Pattern) (selected : d223095 p = 0) : d224608 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222959 q = 0) : d224509 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21952 q selected
    | true =>
      simp only [d222959, d224509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222960 q = 0) : d224510 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222960, d224510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223068 q = 0) : d224584 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223068, d224584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223068, d224584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223069 q = 0) : d224585 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223069, d224585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223069, d224585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223070 q = 0) : d224586 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223070, d224586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223070, d224586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223095 q = 0) : d224608 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223095, d224608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223095, d224608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro21987 (p : Pattern) (selected : d223101 p = 0) : d224614 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222996 q = 0) : d224546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222996, d224546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21960 q selected
    | true =>
      simp only [d222996, d224546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21961 q selected
  have h2 (q : Pattern) (selected : d222997 q = 0) : d224547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222997, d224547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222997, d224547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222998 q = 0) : d224548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222998, d224548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222998, d224548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222999 q = 0) : d224549 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222999, d224549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222999, d224549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223006 q = 0) : d224556 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223006, d224556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21962 q selected
    | true =>
      simp only [d223006, d224556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21963 q selected
  have h6 (q : Pattern) (selected : d223007 q = 0) : d224557 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223007, d224557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223007, d224557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223008 q = 0) : d224558 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223008, d224558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223008, d224558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223032 q = 0) : d224582 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223032, d224582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21968 q selected
    | true =>
      simp only [d223032, d224582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21954 q selected
  have h9 (q : Pattern) (selected : d223066 q = 0) : d224523 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223066, d224523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21975 q selected
    | true =>
      simp only [d223066, d224523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21976 q selected
  have h10 (q : Pattern) (selected : d223067 q = 0) : d224583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223067, d224583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223067, d224583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223072 q = 0) : d224588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223072, d224588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21977 q selected
    | true =>
      simp only [d223072, d224588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223073 q = 0) : d224589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223073, d224589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d223073, d224589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223074 q = 0) : d224590 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223074, d224590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223074, d224590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d223075 q = 0) : d224591 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223075, d224591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223075, d224591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223076 q = 0) : d224592 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223076, d224592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223076, d224592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223080 q = 0) : d224596 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223080, d224596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21979 q selected
    | true =>
      simp only [d223080, d224596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21980 q selected
  have h17 (q : Pattern) (selected : d223081 q = 0) : d224597 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223081, d224597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223081, d224597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d223082 q = 0) : d224598 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223082, d224598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d223082, d224598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d223083 q = 0) : d224599 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223083, d224599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223083, d224599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d223086 q = 0) : d224602 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223086, d224602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21981 q selected
    | true =>
      simp only [d223086, d224602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21982 q selected
  have h21 (q : Pattern) (selected : d223087 q = 0) : d224603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223087, d224603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223087, d224603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d223088 q = 0) : d224604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223088, d224604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d223088, d224604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d223090 q = 0) : d224606 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223090, d224606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21983 q selected
    | true =>
      simp only [d223090, d224606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21957 q selected
  have h24 (q : Pattern) (selected : d223093 q = 0) : d224533 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223093, d224533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21984 q selected
    | true =>
      simp only [d223093, d224533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21985 q selected
  have h25 (q : Pattern) (selected : d223094 q = 0) : d224607 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223094, d224607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d223094, d224607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d223096 q = 0) : d224609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223096, d224609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21986 q selected
    | true =>
      simp only [d223096, d224609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d223097 q = 0) : d224610 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223097, d224610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d223097, d224610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d223098 q = 0) : d224611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223098, d224611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d223098, d224611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d223099 q = 0) : d224612 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223099, d224612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d223099, d224612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d223100 q = 0) : d224613 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223100, d224613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d223100, d224613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d223101 q = 0) : d224614 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223101, d224614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d223101, d224614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro21988 (p : Pattern) (selected : d223108 p = 0) : d224621 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222973 q = 0) : d224523 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222973, d224523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21954 q selected
    | true =>
      simp only [d222973, d224523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21955 q selected
  have h2 (q : Pattern) (selected : d222974 q = 0) : d224524 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222974, d224524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222974, d224524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222975 q = 0) : d224525 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222975, d224525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222975, d224525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222976 q = 0) : d224526 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222976, d224526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222976, d224526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222977 q = 0) : d224527 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222977, d224527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222977, d224527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223103 q = 0) : d224616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223103, d224616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21955 q selected
    | true =>
      simp only [d223103, d224616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223104 q = 0) : d224617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223104, d224617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223104, d224617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223105 q = 0) : d224618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223105, d224618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223105, d224618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223106 q = 0) : d224619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223106, d224619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223106, d224619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223107 q = 0) : d224620 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223107, d224620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223107, d224620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223108 q = 0) : d224621 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223108, d224621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223108, d224621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21989 (p : Pattern) (selected : d223114 p = 0) : d224627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223103 q = 0) : d224616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223103, d224616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21955 q selected
    | true =>
      simp only [d223103, d224616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223104 q = 0) : d224617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223104, d224617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223104, d224617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223105 q = 0) : d224618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223105, d224618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223105, d224618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223106 q = 0) : d224619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223106, d224619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223106, d224619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223107 q = 0) : d224620 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223107, d224620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223107, d224620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223109 q = 0) : d224622 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223109, d224622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21958 q selected
    | true =>
      simp only [d223109, d224622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223110 q = 0) : d224623 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223110, d224623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223110, d224623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223111 q = 0) : d224624 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223111, d224624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223111, d224624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223112 q = 0) : d224625 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223112, d224625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223112, d224625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223113 q = 0) : d224626 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223113, d224626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223113, d224626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223114 q = 0) : d224627 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223114, d224627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223114, d224627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro21990 (p : Pattern) (selected : d223121 p = 0) : d224634 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223090 q = 0) : d224606 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223090, d224606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21983 q selected
    | true =>
      simp only [d223090, d224606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21957 q selected
  have h2 (q : Pattern) (selected : d223093 q = 0) : d224533 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223093, d224533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21984 q selected
    | true =>
      simp only [d223093, d224533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21985 q selected
  have h3 (q : Pattern) (selected : d223094 q = 0) : d224607 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223094, d224607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223094, d224607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223096 q = 0) : d224609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223096, d224609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21986 q selected
    | true =>
      simp only [d223096, d224609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223097 q = 0) : d224610 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223097, d224610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223097, d224610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223098 q = 0) : d224611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223098, d224611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223098, d224611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223119 q = 0) : d224632 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223119, d224632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223119, d224632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223120 q = 0) : d224633 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223120, d224633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223120, d224633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d223121 q = 0) : d224634 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223121, d224634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223121, d224634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro21991 (p : Pattern) (selected : d223123 p = 0) : d224636 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223109 q = 0) : d224622 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223109, d224622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21958 q selected
    | true =>
      simp only [d223109, d224622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223110 q = 0) : d224623 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223110, d224623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223110, d224623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223111 q = 0) : d224624 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223111, d224624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223111, d224624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223112 q = 0) : d224625 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223112, d224625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223112, d224625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223113 q = 0) : d224626 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223113, d224626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223113, d224626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223123 q = 0) : d224636 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223123, d224636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223123, d224636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro21992 (p : Pattern) (selected : d223135 p = 0) : d224648 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117655 q = 0) : d119333 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117655, d119333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117655, d119333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8985 q selected
  have h2 (q : Pattern) (selected : d117527 q = 0) : d119248 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117527, d119248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8985 q selected
    | true =>
      simp only [d117527, d119248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117656 q = 0) : d119334 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117656, d119334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117656, d119334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117528 q = 0) : d119249 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117528, d119249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117528, d119249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117657 q = 0) : d119335 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117657, d119335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117657, d119335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117658 q = 0) : d119336 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117658, d119336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117658, d119336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223129 q = 0) : d224642 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d223129, d224642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223129, d224642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21964 q selected
  have h8 (q : Pattern) (selected : d223009 q = 0) : d224559 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d223009, d224559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21964 q selected
    | true =>
      simp only [d223009, d224559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223130 q = 0) : d224643 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d223130, d224643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223130, d224643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223010 q = 0) : d224560 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d223010, d224560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223010, d224560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d223131 q = 0) : d224644 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d223131, d224644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223131, d224644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d223132 q = 0) : d224645 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d223132, d224645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d223132, d224645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223133 q = 0) : d224646 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223133, d224646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223133, d224646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117672 q = 0) : d119350 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117672, d119350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117672, d119350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8987 q selected
  have h15 (q : Pattern) (selected : d117535 q = 0) : d119256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117535, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8987 q selected
    | true =>
      simp only [d117535, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d117673 q = 0) : d119351 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117673, d119351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d117673, d119351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d117536 q = 0) : d119257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117536, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117536, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d117674 q = 0) : d119352 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117674, d119352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d117674, d119352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d117675 q = 0) : d119353 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117675, d119353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d117675, d119353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d223134 q = 0) : d224647 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223134, d224647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223134, d224647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d223135 q = 0) : d224648 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223135, d224648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223135, d224648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro21993 (p : Pattern) (selected : d223138 p = 0) : d224651 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117659 q = 0) : d119337 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117659, d119337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117659, d119337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8967 q selected
  have h2 (q : Pattern) (selected : d117452 q = 0) : d119173 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117452, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8967 q selected
    | true =>
      simp only [d117452, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117660 q = 0) : d119338 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117660, d119338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117660, d119338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117453 q = 0) : d119174 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117453, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117453, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117661 q = 0) : d119339 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117661, d119339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117661, d119339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117662 q = 0) : d119340 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117662, d119340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117662, d119340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117672 q = 0) : d119350 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117672, d119350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117672, d119350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8987 q selected
  have h8 (q : Pattern) (selected : d117535 q = 0) : d119256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117535, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8987 q selected
    | true =>
      simp only [d117535, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117673 q = 0) : d119351 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117673, d119351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117673, d119351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117536 q = 0) : d119257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117536, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117536, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117674 q = 0) : d119352 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117674, d119352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117674, d119352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117675 q = 0) : d119353 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117675, d119353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117675, d119353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223136 q = 0) : d224649 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223136, d224649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223136, d224649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117681 q = 0) : d119359 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117681, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117681, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8970 q selected
  have h15 (q : Pattern) (selected : d117461 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8970 q selected
    | true =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d117682 q = 0) : d119360 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117682, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d117682, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d117462 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d117683 q = 0) : d119361 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117683, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d117683, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d117684 q = 0) : d119362 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117684, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d117684, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d223137 q = 0) : d224650 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223137, d224650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223137, d224650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d223138 q = 0) : d224651 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223138, d224651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223138, d224651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro21994 (p : Pattern) (selected : d223142 p = 0) : d224655 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117672 q = 0) : d119350 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117672, d119350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117672, d119350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8987 q selected
  have h2 (q : Pattern) (selected : d117535 q = 0) : d119256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117535, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8987 q selected
    | true =>
      simp only [d117535, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117673 q = 0) : d119351 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117673, d119351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117673, d119351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117536 q = 0) : d119257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117536, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117536, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117674 q = 0) : d119352 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117674, d119352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117674, d119352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117675 q = 0) : d119353 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117675, d119353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117675, d119353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117681 q = 0) : d119359 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117681, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117681, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8970 q selected
  have h8 (q : Pattern) (selected : d117461 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8970 q selected
    | true =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117682 q = 0) : d119360 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117682, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117682, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117462 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117683 q = 0) : d119361 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117683, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117683, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117684 q = 0) : d119362 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117684, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117684, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223137 q = 0) : d224650 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223137, d224650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223137, d224650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117689 q = 0) : d119367 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117689, d119367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117689, d119367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d223142 q = 0) : d224655 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223142, d224655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223142, d224655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21995 (p : Pattern) (selected : d223147 p = 0) : d224660 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117664 q = 0) : d119342 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117664, d119342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117664, d119342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8968 q selected
  have h2 (q : Pattern) (selected : d117456 q = 0) : d119177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117456, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8968 q selected
    | true =>
      simp only [d117456, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117665 q = 0) : d119343 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117665, d119343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117665, d119343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117457 q = 0) : d119178 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117457, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117457, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117666 q = 0) : d119344 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117666, d119344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117666, d119344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117667 q = 0) : d119345 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117667, d119345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117667, d119345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117681 q = 0) : d119359 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117681, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117681, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8970 q selected
  have h8 (q : Pattern) (selected : d117461 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8970 q selected
    | true =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117682 q = 0) : d119360 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117682, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117682, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117462 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117683 q = 0) : d119361 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117683, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117683, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117684 q = 0) : d119362 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117684, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117684, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117685 q = 0) : d119363 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117685, d119363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117685, d119363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117689 q = 0) : d119367 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117689, d119367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117689, d119367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d223147 q = 0) : d224660 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223147, d224660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223147, d224660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro21996 (p : Pattern) (selected : d223151 p = 0) : d224664 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117681 q = 0) : d119359 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117681, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117681, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8970 q selected
  have h2 (q : Pattern) (selected : d117461 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8970 q selected
    | true =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117682 q = 0) : d119360 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117682, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117682, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117462 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117683 q = 0) : d119361 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117683, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117683, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117684 q = 0) : d119362 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117684, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117684, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117689 q = 0) : d119367 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117689, d119367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117689, d119367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223151 q = 0) : d224664 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223151, d224664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223151, d224664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro21997 (p : Pattern) (selected : d223157 p = 0) : d224670 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223139 q = 0) : d224652 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223139, d224652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21992 q selected
    | true =>
      simp only [d223139, d224652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21993 q selected
  have h2 (q : Pattern) (selected : d223140 q = 0) : d224653 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223140, d224653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223140, d224653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223141 q = 0) : d224654 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223141, d224654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223141, d224654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223143 q = 0) : d224656 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223143, d224656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21993 q selected
    | true =>
      simp only [d223143, d224656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21994 q selected
  have h5 (q : Pattern) (selected : d223144 q = 0) : d224657 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223144, d224657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223144, d224657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223145 q = 0) : d224658 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223145, d224658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223145, d224658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223146 q = 0) : d224659 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223146, d224659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223146, d224659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223148 q = 0) : d224661 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223148, d224661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21993 q selected
    | true =>
      simp only [d223148, d224661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21995 q selected
  have h9 (q : Pattern) (selected : d223149 q = 0) : d224662 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223149, d224662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223149, d224662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223150 q = 0) : d224663 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223150, d224663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223150, d224663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223152 q = 0) : d224665 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223152, d224665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21995 q selected
    | true =>
      simp only [d223152, d224665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21996 q selected
  have h12 (q : Pattern) (selected : d223153 q = 0) : d224666 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223153, d224666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223153, d224666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223154 q = 0) : d224667 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223154, d224667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223154, d224667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d223155 q = 0) : d224668 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223155, d224668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223155, d224668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223156 q = 0) : d224669 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223156, d224669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223156, d224669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223157 q = 0) : d224670 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223157, d224670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d223157, d224670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro21998 (p : Pattern) (selected : d223162 p = 0) : d224675 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223148 q = 0) : d224661 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223148, d224661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21993 q selected
    | true =>
      simp only [d223148, d224661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21995 q selected
  have h2 (q : Pattern) (selected : d223149 q = 0) : d224662 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223149, d224662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223149, d224662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223150 q = 0) : d224663 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223150, d224663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223150, d224663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223152 q = 0) : d224665 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223152, d224665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21995 q selected
    | true =>
      simp only [d223152, d224665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21996 q selected
  have h5 (q : Pattern) (selected : d223153 q = 0) : d224666 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223153, d224666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223153, d224666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223154 q = 0) : d224667 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223154, d224667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223154, d224667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223155 q = 0) : d224668 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223155, d224668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223155, d224668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223160 q = 0) : d224673 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223160, d224673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223160, d224673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223161 q = 0) : d224674 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223161, d224674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223161, d224674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223162 q = 0) : d224675 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223162, d224675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223162, d224675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro21999 (p : Pattern) (selected : d223168 p = 0) : d224681 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223158 q = 0) : d224671 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223158, d224671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21997 q selected
    | true =>
      simp only [d223158, d224671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223159 q = 0) : d224672 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223159, d224672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223159, d224672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223163 q = 0) : d224676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223163, d224676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21998 q selected
    | true =>
      simp only [d223163, d224676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223164 q = 0) : d224677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223164, d224677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223164, d224677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223165 q = 0) : d224678 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223165, d224678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223165, d224678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223166 q = 0) : d224679 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223166, d224679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223166, d224679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223167 q = 0) : d224680 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223167, d224680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223167, d224680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223168 q = 0) : d224681 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223168, d224681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223168, d224681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
end NetHack.Soko22Hazard87
