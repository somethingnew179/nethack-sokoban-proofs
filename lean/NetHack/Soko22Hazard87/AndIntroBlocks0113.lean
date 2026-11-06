import NetHack.Soko22Hazard87.AndIntroBlocks0112
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro28250 (p : Pattern) (ha : d147907 p = 1) (hb : d149337 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147897 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147898 q = 1) (hb : d149327 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147898, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28248 q ha hb
    | true =>
      simp only [d147898, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d147899 q = 1) (hb : d149328 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147899, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147899, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147900 q = 1) (hb : d149329 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147900, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147900, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147901 q = 1) (hb : d149331 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147901, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147901, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147906 q = 1) (hb : d149336 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147906, d149336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147906, d149336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147907 q = 1) (hb : d149337 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147907, d149337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147907, d149337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro28251 (p : Pattern) (ha : d147913 p = 1) (hb : d149343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147904 q = 1) (hb : d149334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147904, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28249 q ha hb
    | true =>
      simp only [d147904, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147905 q = 1) (hb : d149335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147905, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147905, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d149338 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28250 q ha hb
    | true =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d149339 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147910 q = 1) (hb : d149340 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147910, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147910, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147911 q = 1) (hb : d149341 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147911, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147911, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147912 q = 1) (hb : d149342 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147912, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147912, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147913 q = 1) (hb : d149343 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147913, d149343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147913, d149343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28252 (p : Pattern) (ha : d147917 p = 1) (hb : d149347 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147908 q = 1) (hb : d149338 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28250 q ha hb
    | true =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147909 q = 1) (hb : d149339 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147914 q = 1) (hb : d149344 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147914, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147914, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147915 q = 1) (hb : d149345 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147915, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147915, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147916 q = 1) (hb : d149346 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147916, d149346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147916, d149346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147917 q = 1) (hb : d149347 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147917, d149347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147917, d149347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28253 (p : Pattern) (ha : d147923 p = 1) (hb : d149353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147918 q = 1) (hb : d149348 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147918, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28251 q ha hb
    | true =>
      simp only [d147918, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28252 q ha hb
  have h2 (q : Pattern) (ha : d147919 q = 1) (hb : d149349 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147919, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147919, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147920 q = 1) (hb : d149350 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147920, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147920, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147921 q = 1) (hb : d149351 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147921, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147921, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147922 q = 1) (hb : d149352 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147922, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147922, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147923 q = 1) (hb : d149353 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147923, d149353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147923, d149353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28254 (p : Pattern) (ha : d147926 p = 1) (hb : d149356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147904 q = 1) (hb : d149334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147904, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28249 q ha hb
    | true =>
      simp only [d147904, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147905 q = 1) (hb : d149335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147905, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147905, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d149338 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28250 q ha hb
    | true =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d149339 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147910 q = 1) (hb : d149340 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147910, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147910, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147911 q = 1) (hb : d149341 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147911, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147911, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147912 q = 1) (hb : d149342 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147912, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147912, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147926 q = 1) (hb : d149356 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147926, d149356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147926, d149356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28255 (p : Pattern) (ha : d147927 p = 1) (hb : d149357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147908 q = 1) (hb : d149338 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28250 q ha hb
    | true =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147909 q = 1) (hb : d149339 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147914 q = 1) (hb : d149344 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147914, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147914, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147915 q = 1) (hb : d149345 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147915, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147915, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147916 q = 1) (hb : d149346 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147916, d149346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147916, d149346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147927 q = 1) (hb : d149357 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147927, d149357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147927, d149357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28256 (p : Pattern) (ha : d147933 p = 1) (hb : d149363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147918 q = 1) (hb : d149348 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147918, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28251 q ha hb
    | true =>
      simp only [d147918, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28252 q ha hb
  have h2 (q : Pattern) (ha : d147919 q = 1) (hb : d149349 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147919, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147919, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147920 q = 1) (hb : d149350 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147920, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147920, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147921 q = 1) (hb : d149351 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147921, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147921, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147922 q = 1) (hb : d149352 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147922, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147922, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147928 q = 1) (hb : d149358 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147928, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28254 q ha hb
    | true =>
      simp only [d147928, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28255 q ha hb
  have h7 (q : Pattern) (ha : d147929 q = 1) (hb : d149359 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147929, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147929, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147930 q = 1) (hb : d149360 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147930, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147930, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147931 q = 1) (hb : d149361 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147931, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147931, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147932 q = 1) (hb : d149362 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147932, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147932, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147933 q = 1) (hb : d149363 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147933, d149363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147933, d149363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro28257 (p : Pattern) (ha : d147938 p = 1) (hb : d149368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147904 q = 1) (hb : d149334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147904, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28249 q ha hb
    | true =>
      simp only [d147904, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147905 q = 1) (hb : d149335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147905, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147905, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d149338 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28250 q ha hb
    | true =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d149339 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147910 q = 1) (hb : d149340 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147910, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147910, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147911 q = 1) (hb : d149341 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147911, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147911, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147937 q = 1) (hb : d149367 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147937, d149367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147937, d149367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147938 q = 1) (hb : d149368 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147938, d149368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147938, d149368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28258 (p : Pattern) (ha : d147940 p = 1) (hb : d149370 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147908 q = 1) (hb : d149338 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28250 q ha hb
    | true =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147909 q = 1) (hb : d149339 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147914 q = 1) (hb : d149344 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147914, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147914, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147915 q = 1) (hb : d149345 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147915, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147915, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147939 q = 1) (hb : d149369 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147939, d149369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147939, d149369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147940 q = 1) (hb : d149370 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147940, d149370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147940, d149370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28259 (p : Pattern) (ha : d147947 p = 1) (hb : d149377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147904 q = 1) (hb : d149334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147904, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28249 q ha hb
    | true =>
      simp only [d147904, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147905 q = 1) (hb : d149335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147905, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147905, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d149338 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28250 q ha hb
    | true =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d149339 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147910 q = 1) (hb : d149340 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147910, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147910, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147945 q = 1) (hb : d149375 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147945, d149375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147945, d149375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147946 q = 1) (hb : d149376 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147946, d149376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147946, d149376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147947 q = 1) (hb : d149377 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147947, d149377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147947, d149377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28260 (p : Pattern) (ha : d147950 p = 1) (hb : d149380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147908 q = 1) (hb : d149338 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28250 q ha hb
    | true =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147909 q = 1) (hb : d149339 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147914 q = 1) (hb : d149344 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147914, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147914, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147948 q = 1) (hb : d149378 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147948, d149378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147948, d149378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147949 q = 1) (hb : d149379 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147949, d149379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147949, d149379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147950 q = 1) (hb : d149380 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147950, d149380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147950, d149380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28261 (p : Pattern) (ha : d22312 p = 1) (hb : d147954 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d1204 q = 1) (hb : d52785 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1204, d52785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro173 q ha hb
    | true =>
      simp only [d1204, d52785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1205 q = 1) (hb : d52786 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1205, d52786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1205, d52786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1661 q = 1) (hb : d53102 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1661, d53102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1661, d53102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1662 q = 1) (hb : d53103 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1662, d53103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1662, d53103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1663 q = 1) (hb : d53104 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1663, d53104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1663, d53104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22312 q = 1) (hb : d147954 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22312, d147954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22312, d147954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro28262 (p : Pattern) (ha : d147961 p = 1) (hb : d149384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22313 q = 1) (hb : d147955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22313, d147955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28261 q ha hb
    | true =>
      simp only [d22313, d147955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22314 q = 1) (hb : d147956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22314, d147956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22314, d147956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22315 q = 1) (hb : d147957 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22315, d147957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22315, d147957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22316 q = 1) (hb : d147958 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22316, d147958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22316, d147958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10036 q = 1) (hb : d101463 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23338 q ha hb
    | true =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10038 q = 1) (hb : d101465 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16859 q = 1) (hb : d127633 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16859, d127633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16859, d127633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16860 q = 1) (hb : d127634 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16860, d127634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16860, d127634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22317 q = 1) (hb : d147959 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22317, d147959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22317, d147959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147960 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d147961 q = 1) (hb : d149384 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147961, d149384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147961, d149384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro28263 (p : Pattern) (ha : d147977 p = 1) (hb : d149390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147873 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147962 q = 1) (hb : d149385 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147962, d149385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28262 q ha hb
    | true =>
      simp only [d147962, d149385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d147963 q = 1) (hb : d149386 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147963, d149386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147963, d149386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147964 q = 1) (hb : d149387 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147964, d149387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147964, d149387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147971 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147972 q = 1) (hb : d149323 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147972, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28246 q ha hb
    | true =>
      simp only [d147972, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d147973 q = 1) (hb : d149324 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147973, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147973, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147974 q = 1) (hb : d149325 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147974, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147974, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147975 q = 1) (hb : d149388 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147975, d149388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147975, d149388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147881 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d147882 q = 1) (hb : d149323 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147882, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28246 q ha hb
    | true =>
      simp only [d147882, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d147883 q = 1) (hb : d149324 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147883, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147883, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147884 q = 1) (hb : d149325 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147884, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147884, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147891 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147892 q = 1) (hb : d149327 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147892, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28248 q ha hb
    | true =>
      simp only [d147892, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147893 q = 1) (hb : d149328 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147893, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147893, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147894 q = 1) (hb : d149329 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147894, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147894, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147895 q = 1) (hb : d149330 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147895, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147895, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d147976 q = 1) (hb : d149389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147976, d149389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147976, d149389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d147977 q = 1) (hb : d149390 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147977, d149390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d147977, d149390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro28264 (p : Pattern) (ha : d147982 p = 1) (hb : d149333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147881 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147882 q = 1) (hb : d149323 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147882, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28246 q ha hb
    | true =>
      simp only [d147882, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d147883 q = 1) (hb : d149324 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147883, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147883, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147884 q = 1) (hb : d149325 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147884, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147884, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147891 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147892 q = 1) (hb : d149327 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147892, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28248 q ha hb
    | true =>
      simp only [d147892, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d147893 q = 1) (hb : d149328 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147893, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147893, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147894 q = 1) (hb : d149329 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147894, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147894, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147895 q = 1) (hb : d149330 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147895, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147895, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147980 q = 1) (hb : d149331 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147980, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147980, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d147981 q = 1) (hb : d149332 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147981, d149332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147981, d149332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d147982 q = 1) (hb : d149333 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147982, d149333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d147982, d149333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro28265 (p : Pattern) (ha : d147988 p = 1) (hb : d149396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147978 q = 1) (hb : d149391 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147978, d149391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28263 q ha hb
    | true =>
      simp only [d147978, d149391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147979 q = 1) (hb : d149392 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147979, d149392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147979, d149392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147983 q = 1) (hb : d149334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147983, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28264 q ha hb
    | true =>
      simp only [d147983, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147984 q = 1) (hb : d149335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147984, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147984, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147985 q = 1) (hb : d149393 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147985, d149393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147985, d149393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147986 q = 1) (hb : d149394 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147986, d149394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147986, d149394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147987 q = 1) (hb : d149395 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147987, d149395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147987, d149395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147988 q = 1) (hb : d149396 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147988, d149396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147988, d149396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28266 (p : Pattern) (ha : d147992 p = 1) (hb : d149343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147983 q = 1) (hb : d149334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147983, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28264 q ha hb
    | true =>
      simp only [d147983, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147984 q = 1) (hb : d149335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147984, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147984, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d149338 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28250 q ha hb
    | true =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d149339 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147989 q = 1) (hb : d149340 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147989, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147989, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147990 q = 1) (hb : d149341 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147990, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147990, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147991 q = 1) (hb : d149342 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147991, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147991, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147992 q = 1) (hb : d149343 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147992, d149343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147992, d149343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28267 (p : Pattern) (ha : d148001 p = 1) (hb : d149333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147881 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147882 q = 1) (hb : d149323 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147882, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28246 q ha hb
    | true =>
      simp only [d147882, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d147883 q = 1) (hb : d149324 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147883, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147883, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147884 q = 1) (hb : d149325 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147884, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147884, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147891 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147892 q = 1) (hb : d149327 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147892, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28248 q ha hb
    | true =>
      simp only [d147892, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d147893 q = 1) (hb : d149328 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147893, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147893, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147894 q = 1) (hb : d149329 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147894, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147894, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147895 q = 1) (hb : d149330 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147895, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147895, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147995 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d147996 q = 1) (hb : d149327 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147996, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28248 q ha hb
    | true =>
      simp only [d147996, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d147997 q = 1) (hb : d149328 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147997, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147997, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147998 q = 1) (hb : d149329 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147998, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147998, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147999 q = 1) (hb : d149331 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147999, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147999, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d148000 q = 1) (hb : d149332 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148000, d149332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148000, d149332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148001 q = 1) (hb : d149333 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148001, d149333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148001, d149333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro28268 (p : Pattern) (ha : d148007 p = 1) (hb : d149402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148002 q = 1) (hb : d149334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148002, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28267 q ha hb
    | true =>
      simp only [d148002, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148003 q = 1) (hb : d149335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148003, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148003, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148004 q = 1) (hb : d149399 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148004, d149399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148004, d149399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148005 q = 1) (hb : d149400 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148005, d149400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148005, d149400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148006 q = 1) (hb : d149401 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148006, d149401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148006, d149401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148007 q = 1) (hb : d149402 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148007, d149402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148007, d149402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28269 (p : Pattern) (ha : d148013 p = 1) (hb : d149408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147941 q = 1) (hb : d149371 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147941, d149371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28257 q ha hb
    | true =>
      simp only [d147941, d149371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28258 q ha hb
  have h2 (q : Pattern) (ha : d147942 q = 1) (hb : d149372 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147942, d149372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147942, d149372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147943 q = 1) (hb : d149373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147943, d149373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147943, d149373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147944 q = 1) (hb : d149374 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147944, d149374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147944, d149374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147951 q = 1) (hb : d149381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147951, d149381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28259 q ha hb
    | true =>
      simp only [d147951, d149381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28260 q ha hb
  have h6 (q : Pattern) (ha : d147952 q = 1) (hb : d149382 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147952, d149382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147952, d149382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147953 q = 1) (hb : d149383 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147953, d149383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147953, d149383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147993 q = 1) (hb : d149397 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147993, d149397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28265 q ha hb
    | true =>
      simp only [d147993, d149397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28266 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147918 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d147994 q = 1) (hb : d149398 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147994, d149398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147994, d149398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d148008 q = 1) (hb : d149403 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148008, d149403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28268 q ha hb
    | true =>
      simp only [d148008, d149403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148009 q = 1) (hb : d149404 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148009, d149404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148009, d149404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d148010 q = 1) (hb : d149405 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148010, d149405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148010, d149405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148011 q = 1) (hb : d149406 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148011, d149406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148011, d149406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148012 q = 1) (hb : d149407 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148012, d149407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148012, d149407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148013 q = 1) (hb : d149408 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148013, d149408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148013, d149408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro28270 (p : Pattern) (ha : d148014 p = 1) (hb : d149409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147904 q = 1) (hb : d149334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147904, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28249 q ha hb
    | true =>
      simp only [d147904, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147905 q = 1) (hb : d149335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147905, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147905, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d149338 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28250 q ha hb
    | true =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d149339 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147910 q = 1) (hb : d149340 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147910, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147910, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147911 q = 1) (hb : d149341 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147911, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147911, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147937 q = 1) (hb : d149367 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147937, d149367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147937, d149367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148014 q = 1) (hb : d149409 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148014, d149409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148014, d149409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28271 (p : Pattern) (ha : d148015 p = 1) (hb : d149410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147908 q = 1) (hb : d149338 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28250 q ha hb
    | true =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147909 q = 1) (hb : d149339 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147914 q = 1) (hb : d149344 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147914, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147914, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147915 q = 1) (hb : d149345 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147915, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147915, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147939 q = 1) (hb : d149369 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147939, d149369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147939, d149369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148015 q = 1) (hb : d149410 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148015, d149410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148015, d149410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28272 (p : Pattern) (ha : d148020 p = 1) (hb : d149415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147904 q = 1) (hb : d149334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147904, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28249 q ha hb
    | true =>
      simp only [d147904, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147905 q = 1) (hb : d149335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147905, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147905, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d149338 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28250 q ha hb
    | true =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d149339 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147910 q = 1) (hb : d149340 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147910, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147910, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147945 q = 1) (hb : d149375 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147945, d149375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147945, d149375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147946 q = 1) (hb : d149376 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147946, d149376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147946, d149376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148020 q = 1) (hb : d149415 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148020, d149415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148020, d149415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28273 (p : Pattern) (ha : d148021 p = 1) (hb : d149416 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147908 q = 1) (hb : d149338 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28250 q ha hb
    | true =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147909 q = 1) (hb : d149339 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147914 q = 1) (hb : d149344 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147914, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147914, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147948 q = 1) (hb : d149378 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147948, d149378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147948, d149378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147949 q = 1) (hb : d149379 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147949, d149379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147949, d149379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148021 q = 1) (hb : d149416 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148021, d149416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148021, d149416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28274 (p : Pattern) (ha : d148025 p = 1) (hb : d149420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147978 q = 1) (hb : d149391 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147978, d149391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28263 q ha hb
    | true =>
      simp only [d147978, d149391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147979 q = 1) (hb : d149392 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147979, d149392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147979, d149392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147983 q = 1) (hb : d149334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147983, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28264 q ha hb
    | true =>
      simp only [d147983, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147984 q = 1) (hb : d149335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147984, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147984, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147985 q = 1) (hb : d149393 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147985, d149393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147985, d149393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147986 q = 1) (hb : d149394 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147986, d149394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147986, d149394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147987 q = 1) (hb : d149395 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147987, d149395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147987, d149395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148025 q = 1) (hb : d149420 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148025, d149420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148025, d149420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28275 (p : Pattern) (ha : d148026 p = 1) (hb : d149356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147983 q = 1) (hb : d149334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147983, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28264 q ha hb
    | true =>
      simp only [d147983, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147984 q = 1) (hb : d149335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147984, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147984, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d149338 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28250 q ha hb
    | true =>
      simp only [d147908, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d149339 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147989 q = 1) (hb : d149340 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147989, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147989, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147990 q = 1) (hb : d149341 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147990, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147990, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147991 q = 1) (hb : d149342 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147991, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147991, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148026 q = 1) (hb : d149356 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148026, d149356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148026, d149356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28276 (p : Pattern) (ha : d148029 p = 1) (hb : d149423 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148002 q = 1) (hb : d149334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148002, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28267 q ha hb
    | true =>
      simp only [d148002, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148003 q = 1) (hb : d149335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148003, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148003, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148004 q = 1) (hb : d149399 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148004, d149399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148004, d149399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148005 q = 1) (hb : d149400 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148005, d149400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148005, d149400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148006 q = 1) (hb : d149401 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148006, d149401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148006, d149401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148029 q = 1) (hb : d149423 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148029, d149423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148029, d149423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28277 (p : Pattern) (ha : d148035 p = 1) (hb : d149429 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147941 q = 1) (hb : d149371 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147941, d149371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28257 q ha hb
    | true =>
      simp only [d147941, d149371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28258 q ha hb
  have h2 (q : Pattern) (ha : d147942 q = 1) (hb : d149372 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147942, d149372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147942, d149372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147943 q = 1) (hb : d149373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147943, d149373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147943, d149373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147944 q = 1) (hb : d149374 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147944, d149374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147944, d149374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147951 q = 1) (hb : d149381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147951, d149381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28259 q ha hb
    | true =>
      simp only [d147951, d149381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28260 q ha hb
  have h6 (q : Pattern) (ha : d147952 q = 1) (hb : d149382 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147952, d149382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147952, d149382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147953 q = 1) (hb : d149383 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147953, d149383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147953, d149383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147993 q = 1) (hb : d149397 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147993, d149397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28265 q ha hb
    | true =>
      simp only [d147993, d149397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28266 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147918 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d147994 q = 1) (hb : d149398 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147994, d149398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147994, d149398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d148008 q = 1) (hb : d149403 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148008, d149403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28268 q ha hb
    | true =>
      simp only [d148008, d149403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148009 q = 1) (hb : d149404 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148009, d149404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148009, d149404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d148010 q = 1) (hb : d149405 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148010, d149405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148010, d149405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148011 q = 1) (hb : d149406 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148011, d149406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148011, d149406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148012 q = 1) (hb : d149407 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148012, d149407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148012, d149407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148016 q = 1) (hb : d149411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148016, d149411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28270 q ha hb
    | true =>
      simp only [d148016, d149411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28271 q ha hb
  have h17 (q : Pattern) (ha : d148017 q = 1) (hb : d149412 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148017, d149412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148017, d149412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148018 q = 1) (hb : d149413 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148018, d149413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148018, d149413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d148019 q = 1) (hb : d149414 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148019, d149414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148019, d149414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d148022 q = 1) (hb : d149417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148022, d149417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28272 q ha hb
    | true =>
      simp only [d148022, d149417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28273 q ha hb
  have h21 (q : Pattern) (ha : d148023 q = 1) (hb : d149418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148023, d149418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148023, d149418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d148024 q = 1) (hb : d149419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148024, d149419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d148024, d149419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d148027 q = 1) (hb : d149421 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148027, d149421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28274 q ha hb
    | true =>
      simp only [d148027, d149421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28275 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d147928 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d148028 q = 1) (hb : d149422 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148028, d149422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d148028, d149422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d148030 q = 1) (hb : d149424 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148030, d149424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28276 q ha hb
    | true =>
      simp only [d148030, d149424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d148031 q = 1) (hb : d149425 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148031, d149425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d148031, d149425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d148032 q = 1) (hb : d149426 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148032, d149426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d148032, d149426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d148033 q = 1) (hb : d149427 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148033, d149427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d148033, d149427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d148034 q = 1) (hb : d149428 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148034, d149428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d148034, d149428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d148035 q = 1) (hb : d149429 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148035, d149429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148035, d149429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro28278 (p : Pattern) (ha : d148047 p = 1) (hb : d149436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148037 q = 1) (hb : d149348 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148037, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28266 q ha hb
    | true =>
      simp only [d148037, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28252 q ha hb
  have h2 (q : Pattern) (ha : d148038 q = 1) (hb : d149349 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148038, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148038, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148039 q = 1) (hb : d149350 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148039, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148039, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148040 q = 1) (hb : d149351 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148040, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148040, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148041 q = 1) (hb : d149352 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148041, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148041, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148042 q = 1) (hb : d149431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148042, d149431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28252 q ha hb
    | true =>
      simp only [d148042, d149431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148043 q = 1) (hb : d149432 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148043, d149432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148043, d149432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148044 q = 1) (hb : d149433 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148044, d149433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148044, d149433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148045 q = 1) (hb : d149434 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148045, d149434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148045, d149434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148046 q = 1) (hb : d149435 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148046, d149435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148046, d149435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148047 q = 1) (hb : d149436 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148047, d149436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148047, d149436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro28279 (p : Pattern) (ha : d148053 p = 1) (hb : d149442 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148042 q = 1) (hb : d149431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148042, d149431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28252 q ha hb
    | true =>
      simp only [d148042, d149431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148043 q = 1) (hb : d149432 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148043, d149432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148043, d149432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148044 q = 1) (hb : d149433 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148044, d149433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148044, d149433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148045 q = 1) (hb : d149434 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148045, d149434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148045, d149434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148046 q = 1) (hb : d149435 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148046, d149435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148046, d149435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148048 q = 1) (hb : d149437 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148048, d149437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28255 q ha hb
    | true =>
      simp only [d148048, d149437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148049 q = 1) (hb : d149438 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148049, d149438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148049, d149438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148050 q = 1) (hb : d149439 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148050, d149439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148050, d149439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148051 q = 1) (hb : d149440 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148051, d149440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148051, d149440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148052 q = 1) (hb : d149441 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148052, d149441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148052, d149441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148053 q = 1) (hb : d149442 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148053, d149442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148053, d149442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro28280 (p : Pattern) (ha : d148060 p = 1) (hb : d149449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148027 q = 1) (hb : d149421 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148027, d149421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28274 q ha hb
    | true =>
      simp only [d148027, d149421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28275 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147928 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148028 q = 1) (hb : d149422 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148028, d149422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148028, d149422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d148030 q = 1) (hb : d149424 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148030, d149424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28276 q ha hb
    | true =>
      simp only [d148030, d149424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148031 q = 1) (hb : d149425 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148031, d149425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148031, d149425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148032 q = 1) (hb : d149426 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148032, d149426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148032, d149426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148058 q = 1) (hb : d149447 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148058, d149447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148058, d149447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148059 q = 1) (hb : d149448 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148059, d149448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148059, d149448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148060 q = 1) (hb : d149449 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148060, d149449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148060, d149449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro28281 (p : Pattern) (ha : d148062 p = 1) (hb : d149451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148048 q = 1) (hb : d149437 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148048, d149437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28255 q ha hb
    | true =>
      simp only [d148048, d149437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148049 q = 1) (hb : d149438 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148049, d149438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148049, d149438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148050 q = 1) (hb : d149439 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148050, d149439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148050, d149439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148051 q = 1) (hb : d149440 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148051, d149440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148051, d149440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148052 q = 1) (hb : d149441 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148052, d149441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148052, d149441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148062 q = 1) (hb : d149451 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148062, d149451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148062, d149451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28282 (p : Pattern) (ha : d148078 p = 1) (hb : d149457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22497 q = 1) (hb : d148068 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22497, d148068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22497, d148068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28261 q ha hb
  have h2 (q : Pattern) (ha : d22313 q = 1) (hb : d147955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22313, d147955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28261 q ha hb
    | true =>
      simp only [d22313, d147955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22498 q = 1) (hb : d148069 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22498, d148069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22498, d148069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22314 q = 1) (hb : d147956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22314, d147956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22314, d147956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22499 q = 1) (hb : d148070 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22499, d148070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22499, d148070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22500 q = 1) (hb : d148071 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22500, d148071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22500, d148071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17004 q = 1) (hb : d127738 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23338 q ha hb
  have h8 (q : Pattern) (ha : d10036 q = 1) (hb : d101463 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23338 q ha hb
    | true =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17005 q = 1) (hb : d127739 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d127739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17005, d127739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10038 q = 1) (hb : d101465 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17006 q = 1) (hb : d127740 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17006, d127740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17006, d127740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17007 q = 1) (hb : d127741 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17007, d127741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17007, d127741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22501 q = 1) (hb : d148072 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22501, d148072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22501, d148072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148077 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148078 q = 1) (hb : d149457 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148078, d149457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d148078, d149457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro28283 (p : Pattern) (ha : d148085 p = 1) (hb : d149461 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17004 q = 1) (hb : d127738 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23338 q ha hb
  have h2 (q : Pattern) (ha : d10036 q = 1) (hb : d101463 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23338 q ha hb
    | true =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17005 q = 1) (hb : d127739 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d127739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17005, d127739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10038 q = 1) (hb : d101465 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17006 q = 1) (hb : d127740 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17006, d127740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17006, d127740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17007 q = 1) (hb : d127741 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17007, d127741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17007, d127741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22508 q = 1) (hb : d148079 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22508, d148079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22508, d148079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28245 q ha hb
  have h8 (q : Pattern) (ha : d22220 q = 1) (hb : d147862 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d147862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28245 q ha hb
    | true =>
      simp only [d22220, d147862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22509 q = 1) (hb : d148080 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22509, d148080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22509, d148080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22221 q = 1) (hb : d147863 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d147863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22221, d147863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22510 q = 1) (hb : d148081 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22510, d148081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22510, d148081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22511 q = 1) (hb : d148082 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22511, d148082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22511, d148082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22512 q = 1) (hb : d148083 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22512, d148083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22512, d148083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148084 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148085 q = 1) (hb : d149461 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148085, d149461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d148085, d149461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro28284 (p : Pattern) (ha : d148105 p = 1) (hb : d149466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22508 q = 1) (hb : d148079 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22508, d148079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22508, d148079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28245 q ha hb
  have h2 (q : Pattern) (ha : d22220 q = 1) (hb : d147862 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d147862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28245 q ha hb
    | true =>
      simp only [d22220, d147862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22509 q = 1) (hb : d148080 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22509, d148080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22509, d148080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22221 q = 1) (hb : d147863 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d147863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22221, d147863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22510 q = 1) (hb : d148081 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22510, d148081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22510, d148081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22511 q = 1) (hb : d148082 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22511, d148082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22511, d148082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22529 q = 1) (hb : d148100 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22529, d148100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22529, d148100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28247 q ha hb
  have h8 (q : Pattern) (ha : d22233 q = 1) (hb : d147875 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d147875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28247 q ha hb
    | true =>
      simp only [d22233, d147875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22530 q = 1) (hb : d148101 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22530, d148101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22530, d148101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22234 q = 1) (hb : d147876 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d147876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22234, d147876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22531 q = 1) (hb : d148102 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22531, d148102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22531, d148102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22532 q = 1) (hb : d148103 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22532, d148103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22532, d148103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22533 q = 1) (hb : d148104 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22533, d148104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22533, d148104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148094 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148105 q = 1) (hb : d149466 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148105, d149466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d148105, d149466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro28285 (p : Pattern) (ha : d148120 p = 1) (hb : d149472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148085 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148086 q = 1) (hb : d149458 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148086, d149458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28282 q ha hb
    | true =>
      simp only [d148086, d149458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d148087 q = 1) (hb : d149459 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148087, d149459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148087, d149459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148088 q = 1) (hb : d149460 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148088, d149460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148088, d149460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148095 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148096 q = 1) (hb : d149462 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148096, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28283 q ha hb
    | true =>
      simp only [d148096, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148097 q = 1) (hb : d149463 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148097, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148097, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148098 q = 1) (hb : d149464 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148098, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148098, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148099 q = 1) (hb : d149465 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148099, d149465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148099, d149465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148105 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d148106 q = 1) (hb : d149462 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148106, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28283 q ha hb
    | true =>
      simp only [d148106, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d148107 q = 1) (hb : d149463 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148107, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148107, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148108 q = 1) (hb : d149464 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148108, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148108, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148114 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148115 q = 1) (hb : d149467 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148115, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28284 q ha hb
    | true =>
      simp only [d148115, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148116 q = 1) (hb : d149468 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148116, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148116, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148117 q = 1) (hb : d149469 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148117, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148117, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148118 q = 1) (hb : d149470 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148118, d149470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148118, d149470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d148119 q = 1) (hb : d149471 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148119, d149471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148119, d149471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d148120 q = 1) (hb : d149472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148120, d149472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d148120, d149472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro28286 (p : Pattern) (ha : d148125 p = 1) (hb : d149477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148106 q = 1) (hb : d149462 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148106, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28283 q ha hb
    | true =>
      simp only [d148106, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d148107 q = 1) (hb : d149463 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148107, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148107, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148108 q = 1) (hb : d149464 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148108, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148108, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148114 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148115 q = 1) (hb : d149467 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148115, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28284 q ha hb
    | true =>
      simp only [d148115, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148116 q = 1) (hb : d149468 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148116, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148116, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148117 q = 1) (hb : d149469 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148117, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148117, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148118 q = 1) (hb : d149470 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148118, d149470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148118, d149470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148123 q = 1) (hb : d149475 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148123, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148123, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d148124 q = 1) (hb : d149476 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148124, d149476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148124, d149476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d148125 q = 1) (hb : d149477 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148125, d149477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148125, d149477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro28287 (p : Pattern) (ha : d148131 p = 1) (hb : d149483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148121 q = 1) (hb : d149473 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148121, d149473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28285 q ha hb
    | true =>
      simp only [d148121, d149473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148122 q = 1) (hb : d149474 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148122, d149474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148122, d149474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148126 q = 1) (hb : d149478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148126, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28286 q ha hb
    | true =>
      simp only [d148126, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148127 q = 1) (hb : d149479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148127, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148127, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148128 q = 1) (hb : d149480 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148128, d149480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148128, d149480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148129 q = 1) (hb : d149481 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148129, d149481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148129, d149481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148130 q = 1) (hb : d149482 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148130, d149482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148130, d149482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148131 q = 1) (hb : d149483 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148131, d149483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148131, d149483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28288 (p : Pattern) (ha : d148139 p = 1) (hb : d149485 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148133 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148134 q = 1) (hb : d149467 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148134, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28284 q ha hb
    | true =>
      simp only [d148134, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d148135 q = 1) (hb : d149468 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148135, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148135, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148136 q = 1) (hb : d149469 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148136, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148136, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148137 q = 1) (hb : d149475 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148137, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148137, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148138 q = 1) (hb : d149484 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148138, d149484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148138, d149484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148139 q = 1) (hb : d149485 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148139, d149485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148139, d149485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro28289 (p : Pattern) (ha : d148145 p = 1) (hb : d149491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148126 q = 1) (hb : d149478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148126, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28286 q ha hb
    | true =>
      simp only [d148126, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148127 q = 1) (hb : d149479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148127, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148127, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148140 q = 1) (hb : d149486 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148140, d149486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28288 q ha hb
    | true =>
      simp only [d148140, d149486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148141 q = 1) (hb : d149487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148141, d149487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148141, d149487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148142 q = 1) (hb : d149488 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148142, d149488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148142, d149488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148143 q = 1) (hb : d149489 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148143, d149489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148143, d149489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148144 q = 1) (hb : d149490 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148144, d149490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148144, d149490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148145 q = 1) (hb : d149491 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148145, d149491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148145, d149491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28290 (p : Pattern) (ha : d148167 p = 1) (hb : d149477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148106 q = 1) (hb : d149462 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148106, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28283 q ha hb
    | true =>
      simp only [d148106, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d148107 q = 1) (hb : d149463 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148107, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148107, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148108 q = 1) (hb : d149464 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148108, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148108, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148114 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148115 q = 1) (hb : d149467 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148115, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28284 q ha hb
    | true =>
      simp only [d148115, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148116 q = 1) (hb : d149468 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148116, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148116, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148117 q = 1) (hb : d149469 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148117, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148117, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148118 q = 1) (hb : d149470 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148118, d149470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148118, d149470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148161 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d148162 q = 1) (hb : d149467 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148162, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28284 q ha hb
    | true =>
      simp only [d148162, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d148163 q = 1) (hb : d149468 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148163, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148163, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148164 q = 1) (hb : d149469 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148164, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148164, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148165 q = 1) (hb : d149475 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148165, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148165, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d148166 q = 1) (hb : d149476 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148166, d149476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148166, d149476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148167 q = 1) (hb : d149477 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148167, d149477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148167, d149477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro28291 (p : Pattern) (ha : d148173 p = 1) (hb : d149497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148168 q = 1) (hb : d149478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148168, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28290 q ha hb
    | true =>
      simp only [d148168, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148169 q = 1) (hb : d149479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148169, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148169, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148170 q = 1) (hb : d149494 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148170, d149494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148170, d149494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148171 q = 1) (hb : d149495 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148171, d149495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148171, d149495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148172 q = 1) (hb : d149496 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148172, d149496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148172, d149496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148173 q = 1) (hb : d149497 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148173, d149497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148173, d149497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28292 (p : Pattern) (ha : d148179 p = 1) (hb : d149503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148146 q = 1) (hb : d149492 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148146, d149492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28287 q ha hb
    | true =>
      simp only [d148146, d149492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28289 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148159 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148160 q = 1) (hb : d149493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148160, d149493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148160, d149493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d148174 q = 1) (hb : d149498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148174, d149498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28291 q ha hb
    | true =>
      simp only [d148174, d149498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148175 q = 1) (hb : d149499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148175, d149499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148175, d149499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148176 q = 1) (hb : d149500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148176, d149500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148176, d149500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148177 q = 1) (hb : d149501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148177, d149501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148177, d149501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148178 q = 1) (hb : d149502 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148178, d149502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148178, d149502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148179 q = 1) (hb : d149503 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148179, d149503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148179, d149503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro28293 (p : Pattern) (ha : d148158 p = 1) (hb : d149508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148140 q = 1) (hb : d149486 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148140, d149486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28288 q ha hb
    | true =>
      simp only [d148140, d149486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148141 q = 1) (hb : d149487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148141, d149487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148141, d149487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148155 q = 1) (hb : d149505 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148155, d149505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148155, d149505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148156 q = 1) (hb : d149506 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148156, d149506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148156, d149506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148157 q = 1) (hb : d149507 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148157, d149507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148157, d149507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148158 q = 1) (hb : d149508 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148158, d149508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148158, d149508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28294 (p : Pattern) (ha : d148186 p = 1) (hb : d149514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148181 q = 1) (hb : d149509 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148181, d149509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28293 q ha hb
    | true =>
      simp only [d148181, d149509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148182 q = 1) (hb : d149510 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148182, d149510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148182, d149510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148183 q = 1) (hb : d149511 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148183, d149511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148183, d149511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148184 q = 1) (hb : d149512 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148184, d149512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148184, d149512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148185 q = 1) (hb : d149513 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148185, d149513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148185, d149513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148186 q = 1) (hb : d149514 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148186, d149514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148186, d149514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28295 (p : Pattern) (ha : d148192 p = 1) (hb : d149520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147924 q = 1) (hb : d149354 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147924, d149354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147924, d149354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28253 q ha hb
  have h2 (q : Pattern) (ha : d147925 q = 1) (hb : d149355 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147925, d149355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147925, d149355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d147934 q = 1) (hb : d149364 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147934, d149364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28253 q ha hb
    | true =>
      simp only [d147934, d149364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28256 q ha hb
  have h4 (q : Pattern) (ha : d147935 q = 1) (hb : d149365 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147935, d149365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147935, d149365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147936 q = 1) (hb : d149366 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147936, d149366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147936, d149366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148036 q = 1) (hb : d149430 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148036, d149430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28269 q ha hb
    | true =>
      simp only [d148036, d149430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28277 q ha hb
  have h7 (q : Pattern) (ha : d148054 q = 1) (hb : d149443 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148054, d149443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28278 q ha hb
    | true =>
      simp only [d148054, d149443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28279 q ha hb
  have h8 (q : Pattern) (ha : d148055 q = 1) (hb : d149444 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148055, d149444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148055, d149444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148056 q = 1) (hb : d149445 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148056, d149445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148056, d149445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d148057 q = 1) (hb : d149446 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148057, d149446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148057, d149446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148061 q = 1) (hb : d149450 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148061, d149450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148061, d149450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28280 q ha hb
  have h12 (q : Pattern) (ha : d148063 q = 1) (hb : d149452 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148063, d149452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148063, d149452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28281 q ha hb
  have h13 (q : Pattern) (ha : d148064 q = 1) (hb : d149453 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148064, d149453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148064, d149453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148065 q = 1) (hb : d149454 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148065, d149454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148065, d149454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d148066 q = 1) (hb : d149455 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148066, d149455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d148066, d149455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d148067 q = 1) (hb : d149456 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148067, d149456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148067, d149456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148180 q = 1) (hb : d149504 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148180, d149504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148180, d149504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28292 q ha hb
  have h18 (q : Pattern) (ha : d148187 q = 1) (hb : d149515 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148187, d149515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148187, d149515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28294 q ha hb
  have h19 (q : Pattern) (ha : d148188 q = 1) (hb : d149516 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148188, d149516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148188, d149516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d148189 q = 1) (hb : d149517 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148189, d149517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d148189, d149517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d148190 q = 1) (hb : d149518 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148190, d149518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d148190, d149518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d148191 q = 1) (hb : d149519 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148191, d149519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d148191, d149519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d148192 q = 1) (hb : d149520 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d148192, d149520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d148192, d149520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro28296 (p : Pattern) (ha : d148198 p = 1) (hb : d149526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148193 q = 1) (hb : d149521 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d148193, d149521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148193, d149521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28295 q ha hb
  have h2 (q : Pattern) (ha : d148194 q = 1) (hb : d149522 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d148194, d149522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148194, d149522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148195 q = 1) (hb : d149523 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d148195, d149523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148195, d149523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148196 q = 1) (hb : d149524 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d148196, d149524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148196, d149524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148197 q = 1) (hb : d149525 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d148197, d149525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148197, d149525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148198 q = 1) (hb : d149526 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d148198, d149526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148198, d149526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28297 (p : Pattern) (ha : d148204 p = 1) (hb : d149531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10343 q = 1) (hb : d101664 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
    | true =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10345 q = 1) (hb : d101666 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17225 q = 1) (hb : d127927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17225, d127927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17225, d127927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17226 q = 1) (hb : d127928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17226, d127928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17226, d127928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10364 q = 1) (hb : d101685 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
    | true =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10366 q = 1) (hb : d101687 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17153 q = 1) (hb : d127855 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d127855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17153, d127855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17154 q = 1) (hb : d127856 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, d127856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17154, d127856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22685 q = 1) (hb : d148203 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22685, d148203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22685, d148203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d113872 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d148204 q = 1) (hb : d149531 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148204, d149531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d148204, d149531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro28298 (p : Pattern) (ha : d22687 p = 1) (hb : d148205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2020 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro259 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2024 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro260 q ha hb
  have h3 (q : Pattern) (ha : d2025 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2041 q = 1) (hb : d53320 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro263 q ha hb
    | true =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h5 (q : Pattern) (ha : d2043 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
  have h6 (q : Pattern) (ha : d2044 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2045 q = 1) (hb : d53324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2045, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2045, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2029 q = 1) (hb : d53308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d2030 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d2049 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2050 q = 1) (hb : d53329 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2050, d53329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2050, d53329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2051 q = 1) (hb : d53330 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2051, d53330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2051, d53330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d22687 q = 1) (hb : d148205 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22687, d148205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22687, d148205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h15 p ha hb
theorem andIntro28299 (p : Pattern) (ha : d148212 p = 1) (hb : d149535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10364 q = 1) (hb : d101685 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
    | true =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10366 q = 1) (hb : d101687 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17153 q = 1) (hb : d127855 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d127855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17153, d127855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17154 q = 1) (hb : d127856 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, d127856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17154, d127856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22688 q = 1) (hb : d148206 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d148206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28298 q ha hb
    | true =>
      simp only [d22688, d148206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22689 q = 1) (hb : d148207 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d148207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22689, d148207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22690 q = 1) (hb : d148208 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22690, d148208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22690, d148208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22691 q = 1) (hb : d148209 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22691, d148209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22691, d148209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22692 q = 1) (hb : d148210 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22692, d148210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22692, d148210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148211 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d148212 q = 1) (hb : d149535 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148212, d149535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d148212, d149535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro28300 (p : Pattern) (ha : d148234 p = 1) (hb : d149542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148212 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148213 q = 1) (hb : d149532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148213, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28297 q ha hb
    | true =>
      simp only [d148213, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d148214 q = 1) (hb : d149533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148214, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148214, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148215 q = 1) (hb : d149534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148215, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148215, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148222 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148223 q = 1) (hb : d149536 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148223, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28299 q ha hb
    | true =>
      simp only [d148223, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148224 q = 1) (hb : d149537 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148224, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148224, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148225 q = 1) (hb : d149538 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148225, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148225, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148226 q = 1) (hb : d149539 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148226, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148226, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148228 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d148229 q = 1) (hb : d149536 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148229, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28299 q ha hb
    | true =>
      simp only [d148229, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d148230 q = 1) (hb : d149537 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148230, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148230, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148231 q = 1) (hb : d149538 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148231, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148231, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148232 q = 1) (hb : d149540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148232, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148232, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d148233 q = 1) (hb : d149541 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148233, d149541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148233, d149541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148234 q = 1) (hb : d149542 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148234, d149542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148234, d149542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro28301 (p : Pattern) (ha : d148238 p = 1) (hb : d149546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148228 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148229 q = 1) (hb : d149536 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148229, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28299 q ha hb
    | true =>
      simp only [d148229, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d148230 q = 1) (hb : d149537 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148230, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148230, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148231 q = 1) (hb : d149538 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148231, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148231, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148232 q = 1) (hb : d149540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148232, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148232, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148237 q = 1) (hb : d149545 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148237, d149545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148237, d149545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148238 q = 1) (hb : d149546 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148238, d149546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148238, d149546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro28302 (p : Pattern) (ha : d148244 p = 1) (hb : d149552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148235 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148235, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28300 q ha hb
    | true =>
      simp only [d148235, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148236 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148236, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148236, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28301 q ha hb
    | true =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148241 q = 1) (hb : d149549 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148241, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148241, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148242 q = 1) (hb : d149550 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148242, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148242, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148243 q = 1) (hb : d149551 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148243, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148243, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148244 q = 1) (hb : d149552 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148244, d149552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148244, d149552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28303 (p : Pattern) (ha : d148248 p = 1) (hb : d149556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148239 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28301 q ha hb
    | true =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148240 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148245 q = 1) (hb : d149553 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148245, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148245, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148246 q = 1) (hb : d149554 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148246, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148246, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148247 q = 1) (hb : d149555 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148247, d149555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148247, d149555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148248 q = 1) (hb : d149556 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148248, d149556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148248, d149556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28304 (p : Pattern) (ha : d148254 p = 1) (hb : d149562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148249 q = 1) (hb : d149557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148249, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28302 q ha hb
    | true =>
      simp only [d148249, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28303 q ha hb
  have h2 (q : Pattern) (ha : d148250 q = 1) (hb : d149558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148250, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148250, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148251 q = 1) (hb : d149559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148251, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148251, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148252 q = 1) (hb : d149560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148252, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148252, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148253 q = 1) (hb : d149561 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148253, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148253, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148254 q = 1) (hb : d149562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148254, d149562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148254, d149562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28305 (p : Pattern) (ha : d148257 p = 1) (hb : d149565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148235 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148235, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28300 q ha hb
    | true =>
      simp only [d148235, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148236 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148236, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148236, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28301 q ha hb
    | true =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148241 q = 1) (hb : d149549 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148241, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148241, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148242 q = 1) (hb : d149550 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148242, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148242, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148243 q = 1) (hb : d149551 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148243, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148243, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148257 q = 1) (hb : d149565 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148257, d149565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148257, d149565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28306 (p : Pattern) (ha : d148258 p = 1) (hb : d149566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148239 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28301 q ha hb
    | true =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148240 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148245 q = 1) (hb : d149553 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148245, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148245, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148246 q = 1) (hb : d149554 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148246, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148246, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148247 q = 1) (hb : d149555 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148247, d149555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148247, d149555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148258 q = 1) (hb : d149566 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148258, d149566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148258, d149566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28307 (p : Pattern) (ha : d148264 p = 1) (hb : d149572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148249 q = 1) (hb : d149557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148249, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28302 q ha hb
    | true =>
      simp only [d148249, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28303 q ha hb
  have h2 (q : Pattern) (ha : d148250 q = 1) (hb : d149558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148250, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148250, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148251 q = 1) (hb : d149559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148251, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148251, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148252 q = 1) (hb : d149560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148252, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148252, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148253 q = 1) (hb : d149561 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148253, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148253, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148259 q = 1) (hb : d149567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148259, d149567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28305 q ha hb
    | true =>
      simp only [d148259, d149567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28306 q ha hb
  have h7 (q : Pattern) (ha : d148260 q = 1) (hb : d149568 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148260, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148260, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148261 q = 1) (hb : d149569 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148261, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148261, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148262 q = 1) (hb : d149570 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148262, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148262, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148263 q = 1) (hb : d149571 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148263, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148263, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148264 q = 1) (hb : d149572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148264, d149572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148264, d149572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro28308 (p : Pattern) (ha : d148269 p = 1) (hb : d149577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148235 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148235, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28300 q ha hb
    | true =>
      simp only [d148235, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148236 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148236, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148236, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28301 q ha hb
    | true =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148241 q = 1) (hb : d149549 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148241, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148241, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148242 q = 1) (hb : d149550 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148242, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148242, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148268 q = 1) (hb : d149576 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148268, d149576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148268, d149576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148269 q = 1) (hb : d149577 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148269, d149577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148269, d149577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28309 (p : Pattern) (ha : d148271 p = 1) (hb : d149579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148239 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28301 q ha hb
    | true =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148240 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148245 q = 1) (hb : d149553 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148245, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148245, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148246 q = 1) (hb : d149554 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148246, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148246, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148270 q = 1) (hb : d149578 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148270, d149578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148270, d149578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148271 q = 1) (hb : d149579 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148271, d149579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148271, d149579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28310 (p : Pattern) (ha : d148278 p = 1) (hb : d149586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148235 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148235, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28300 q ha hb
    | true =>
      simp only [d148235, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148236 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148236, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148236, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28301 q ha hb
    | true =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148241 q = 1) (hb : d149549 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148241, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148241, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148276 q = 1) (hb : d149584 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148276, d149584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148276, d149584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148277 q = 1) (hb : d149585 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148277, d149585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148277, d149585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148278 q = 1) (hb : d149586 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148278, d149586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148278, d149586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28311 (p : Pattern) (ha : d148281 p = 1) (hb : d149589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148239 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28301 q ha hb
    | true =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148240 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148245 q = 1) (hb : d149553 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148245, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148245, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148279 q = 1) (hb : d149587 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148279, d149587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148279, d149587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148280 q = 1) (hb : d149588 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148280, d149588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148280, d149588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148281 q = 1) (hb : d149589 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148281, d149589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148281, d149589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28312 (p : Pattern) (ha : d148286 p = 1) (hb : d149593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10343 q = 1) (hb : d101664 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
    | true =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10345 q = 1) (hb : d101666 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17225 q = 1) (hb : d127927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17225, d127927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17225, d127927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17226 q = 1) (hb : d127928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17226, d127928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17226, d127928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22767 q = 1) (hb : d148285 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22767, d148285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22767, d148285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127930 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d148286 q = 1) (hb : d149593 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148286, d149593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d148286, d149593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro28313 (p : Pattern) (ha : d148296 p = 1) (hb : d149599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148204 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148287 q = 1) (hb : d149594 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148287, d149594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28312 q ha hb
    | true =>
      simp only [d148287, d149594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d148288 q = 1) (hb : d149595 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148288, d149595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148288, d149595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148289 q = 1) (hb : d149596 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148289, d149596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148289, d149596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148290 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148291 q = 1) (hb : d149532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148291, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28297 q ha hb
    | true =>
      simp only [d148291, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148292 q = 1) (hb : d149533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148292, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148292, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148293 q = 1) (hb : d149534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148293, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148293, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148294 q = 1) (hb : d149597 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148294, d149597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148294, d149597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148212 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d148213 q = 1) (hb : d149532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148213, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28297 q ha hb
    | true =>
      simp only [d148213, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d148214 q = 1) (hb : d149533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148214, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148214, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148215 q = 1) (hb : d149534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148215, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148215, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148222 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148223 q = 1) (hb : d149536 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148223, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28299 q ha hb
    | true =>
      simp only [d148223, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148224 q = 1) (hb : d149537 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148224, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148224, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148225 q = 1) (hb : d149538 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148225, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148225, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148226 q = 1) (hb : d149539 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148226, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148226, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d148295 q = 1) (hb : d149598 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148295, d149598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148295, d149598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d148296 q = 1) (hb : d149599 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148296, d149599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d148296, d149599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro28314 (p : Pattern) (ha : d148301 p = 1) (hb : d149542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148212 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148213 q = 1) (hb : d149532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148213, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28297 q ha hb
    | true =>
      simp only [d148213, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d148214 q = 1) (hb : d149533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148214, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148214, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148215 q = 1) (hb : d149534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148215, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148215, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148222 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148223 q = 1) (hb : d149536 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148223, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28299 q ha hb
    | true =>
      simp only [d148223, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148224 q = 1) (hb : d149537 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148224, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148224, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148225 q = 1) (hb : d149538 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148225, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148225, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148226 q = 1) (hb : d149539 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148226, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148226, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148299 q = 1) (hb : d149540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148299, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148299, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d148300 q = 1) (hb : d149541 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148300, d149541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148300, d149541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d148301 q = 1) (hb : d149542 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148301, d149542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148301, d149542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro28315 (p : Pattern) (ha : d148307 p = 1) (hb : d149605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148297 q = 1) (hb : d149600 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148297, d149600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28313 q ha hb
    | true =>
      simp only [d148297, d149600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148298 q = 1) (hb : d149601 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148298, d149601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148298, d149601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148302 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148302, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28314 q ha hb
    | true =>
      simp only [d148302, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148303 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148303, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148303, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148304 q = 1) (hb : d149602 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148304, d149602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148304, d149602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148305 q = 1) (hb : d149603 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148305, d149603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148305, d149603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148306 q = 1) (hb : d149604 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148306, d149604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148306, d149604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148307 q = 1) (hb : d149605 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148307, d149605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148307, d149605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28316 (p : Pattern) (ha : d148311 p = 1) (hb : d149552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148302 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148302, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28314 q ha hb
    | true =>
      simp only [d148302, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148303 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148303, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148303, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28301 q ha hb
    | true =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148308 q = 1) (hb : d149549 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148308, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148308, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148309 q = 1) (hb : d149550 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148309, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148309, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148310 q = 1) (hb : d149551 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148310, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148310, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148311 q = 1) (hb : d149552 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148311, d149552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148311, d149552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28317 (p : Pattern) (ha : d148320 p = 1) (hb : d149542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148212 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148213 q = 1) (hb : d149532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148213, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28297 q ha hb
    | true =>
      simp only [d148213, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d148214 q = 1) (hb : d149533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148214, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148214, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148215 q = 1) (hb : d149534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148215, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148215, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148222 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148223 q = 1) (hb : d149536 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148223, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28299 q ha hb
    | true =>
      simp only [d148223, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148224 q = 1) (hb : d149537 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148224, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148224, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148225 q = 1) (hb : d149538 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148225, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148225, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148226 q = 1) (hb : d149539 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148226, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148226, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148314 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d148315 q = 1) (hb : d149536 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148315, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28299 q ha hb
    | true =>
      simp only [d148315, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d148316 q = 1) (hb : d149537 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148316, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148316, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148317 q = 1) (hb : d149538 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148317, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148317, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148318 q = 1) (hb : d149540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148318, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148318, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d148319 q = 1) (hb : d149541 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148319, d149541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148319, d149541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148320 q = 1) (hb : d149542 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148320, d149542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148320, d149542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro28318 (p : Pattern) (ha : d148326 p = 1) (hb : d149611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148321 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148321, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28317 q ha hb
    | true =>
      simp only [d148321, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148322 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148322, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148322, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148323 q = 1) (hb : d149608 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148323, d149608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148323, d149608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148324 q = 1) (hb : d149609 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148324, d149609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148324, d149609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148325 q = 1) (hb : d149610 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148325, d149610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148325, d149610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148326 q = 1) (hb : d149611 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148326, d149611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148326, d149611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28319 (p : Pattern) (ha : d148332 p = 1) (hb : d149617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148272 q = 1) (hb : d149580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148272, d149580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28308 q ha hb
    | true =>
      simp only [d148272, d149580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28309 q ha hb
  have h2 (q : Pattern) (ha : d148273 q = 1) (hb : d149581 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148273, d149581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148273, d149581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148274 q = 1) (hb : d149582 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148274, d149582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148274, d149582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148275 q = 1) (hb : d149583 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148275, d149583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148275, d149583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148282 q = 1) (hb : d149590 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148282, d149590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28310 q ha hb
    | true =>
      simp only [d148282, d149590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28311 q ha hb
  have h6 (q : Pattern) (ha : d148283 q = 1) (hb : d149591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148283, d149591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148283, d149591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148284 q = 1) (hb : d149592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148284, d149592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148284, d149592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148312 q = 1) (hb : d149606 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148312, d149606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28315 q ha hb
    | true =>
      simp only [d148312, d149606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28316 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d148249 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d148313 q = 1) (hb : d149607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148313, d149607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148313, d149607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d148327 q = 1) (hb : d149612 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148327, d149612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28318 q ha hb
    | true =>
      simp only [d148327, d149612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148328 q = 1) (hb : d149613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148328, d149613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148328, d149613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d148329 q = 1) (hb : d149614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148329, d149614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148329, d149614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148330 q = 1) (hb : d149615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148330, d149615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148330, d149615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148331 q = 1) (hb : d149616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148331, d149616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148331, d149616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148332 q = 1) (hb : d149617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148332, d149617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148332, d149617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro28320 (p : Pattern) (ha : d148333 p = 1) (hb : d149618 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148235 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148235, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28300 q ha hb
    | true =>
      simp only [d148235, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148236 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148236, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148236, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28301 q ha hb
    | true =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148241 q = 1) (hb : d149549 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148241, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148241, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148242 q = 1) (hb : d149550 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148242, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148242, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148268 q = 1) (hb : d149576 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148268, d149576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148268, d149576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148333 q = 1) (hb : d149618 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148333, d149618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148333, d149618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28321 (p : Pattern) (ha : d148334 p = 1) (hb : d149619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148239 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28301 q ha hb
    | true =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148240 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148245 q = 1) (hb : d149553 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148245, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148245, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148246 q = 1) (hb : d149554 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148246, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148246, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148270 q = 1) (hb : d149578 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148270, d149578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148270, d149578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148334 q = 1) (hb : d149619 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148334, d149619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148334, d149619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28322 (p : Pattern) (ha : d148339 p = 1) (hb : d149624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148235 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148235, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28300 q ha hb
    | true =>
      simp only [d148235, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148236 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148236, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148236, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28301 q ha hb
    | true =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148241 q = 1) (hb : d149549 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148241, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148241, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148276 q = 1) (hb : d149584 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148276, d149584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148276, d149584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148277 q = 1) (hb : d149585 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148277, d149585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148277, d149585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148339 q = 1) (hb : d149624 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148339, d149624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148339, d149624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28323 (p : Pattern) (ha : d148340 p = 1) (hb : d149625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148239 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28301 q ha hb
    | true =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148240 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148245 q = 1) (hb : d149553 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148245, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148245, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148279 q = 1) (hb : d149587 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148279, d149587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148279, d149587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148280 q = 1) (hb : d149588 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148280, d149588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148280, d149588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148340 q = 1) (hb : d149625 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148340, d149625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148340, d149625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28324 (p : Pattern) (ha : d148344 p = 1) (hb : d149629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148297 q = 1) (hb : d149600 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148297, d149600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28313 q ha hb
    | true =>
      simp only [d148297, d149600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148298 q = 1) (hb : d149601 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148298, d149601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148298, d149601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148302 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148302, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28314 q ha hb
    | true =>
      simp only [d148302, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148303 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148303, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148303, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148304 q = 1) (hb : d149602 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148304, d149602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148304, d149602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148305 q = 1) (hb : d149603 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148305, d149603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148305, d149603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148306 q = 1) (hb : d149604 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148306, d149604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148306, d149604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148344 q = 1) (hb : d149629 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148344, d149629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148344, d149629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28325 (p : Pattern) (ha : d148345 p = 1) (hb : d149565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148302 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148302, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28314 q ha hb
    | true =>
      simp only [d148302, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148303 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148303, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148303, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28301 q ha hb
    | true =>
      simp only [d148239, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148308 q = 1) (hb : d149549 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148308, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148308, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148309 q = 1) (hb : d149550 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148309, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148309, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148310 q = 1) (hb : d149551 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148310, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148310, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148345 q = 1) (hb : d149565 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148345, d149565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148345, d149565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28326 (p : Pattern) (ha : d148348 p = 1) (hb : d149632 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148321 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148321, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28317 q ha hb
    | true =>
      simp only [d148321, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148322 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148322, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148322, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148323 q = 1) (hb : d149608 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148323, d149608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148323, d149608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148324 q = 1) (hb : d149609 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148324, d149609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148324, d149609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148325 q = 1) (hb : d149610 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148325, d149610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148325, d149610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148348 q = 1) (hb : d149632 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148348, d149632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148348, d149632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28327 (p : Pattern) (ha : d148354 p = 1) (hb : d149638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148272 q = 1) (hb : d149580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148272, d149580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28308 q ha hb
    | true =>
      simp only [d148272, d149580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28309 q ha hb
  have h2 (q : Pattern) (ha : d148273 q = 1) (hb : d149581 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148273, d149581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148273, d149581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148274 q = 1) (hb : d149582 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148274, d149582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148274, d149582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148275 q = 1) (hb : d149583 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148275, d149583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148275, d149583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148282 q = 1) (hb : d149590 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148282, d149590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28310 q ha hb
    | true =>
      simp only [d148282, d149590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28311 q ha hb
  have h6 (q : Pattern) (ha : d148283 q = 1) (hb : d149591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148283, d149591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148283, d149591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148284 q = 1) (hb : d149592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148284, d149592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148284, d149592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148312 q = 1) (hb : d149606 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148312, d149606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28315 q ha hb
    | true =>
      simp only [d148312, d149606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28316 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d148249 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d148313 q = 1) (hb : d149607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148313, d149607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148313, d149607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d148327 q = 1) (hb : d149612 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148327, d149612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28318 q ha hb
    | true =>
      simp only [d148327, d149612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148328 q = 1) (hb : d149613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148328, d149613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148328, d149613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d148329 q = 1) (hb : d149614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148329, d149614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148329, d149614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148330 q = 1) (hb : d149615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148330, d149615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148330, d149615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148331 q = 1) (hb : d149616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148331, d149616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148331, d149616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148335 q = 1) (hb : d149620 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148335, d149620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28320 q ha hb
    | true =>
      simp only [d148335, d149620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28321 q ha hb
  have h17 (q : Pattern) (ha : d148336 q = 1) (hb : d149621 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148336, d149621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148336, d149621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148337 q = 1) (hb : d149622 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148337, d149622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148337, d149622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d148338 q = 1) (hb : d149623 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148338, d149623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148338, d149623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d148341 q = 1) (hb : d149626 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148341, d149626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28322 q ha hb
    | true =>
      simp only [d148341, d149626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28323 q ha hb
  have h21 (q : Pattern) (ha : d148342 q = 1) (hb : d149627 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148342, d149627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148342, d149627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d148343 q = 1) (hb : d149628 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148343, d149628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d148343, d149628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d148346 q = 1) (hb : d149630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148346, d149630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28324 q ha hb
    | true =>
      simp only [d148346, d149630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28325 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d148259 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d148347 q = 1) (hb : d149631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148347, d149631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d148347, d149631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d148349 q = 1) (hb : d149633 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148349, d149633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28326 q ha hb
    | true =>
      simp only [d148349, d149633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d148350 q = 1) (hb : d149634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148350, d149634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d148350, d149634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d148351 q = 1) (hb : d149635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148351, d149635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d148351, d149635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d148352 q = 1) (hb : d149636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148352, d149636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d148352, d149636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d148353 q = 1) (hb : d149637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148353, d149637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d148353, d149637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d148354 q = 1) (hb : d149638 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148354, d149638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148354, d149638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro28328 (p : Pattern) (ha : d148366 p = 1) (hb : d149645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148356 q = 1) (hb : d149557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148356, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28316 q ha hb
    | true =>
      simp only [d148356, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28303 q ha hb
  have h2 (q : Pattern) (ha : d148357 q = 1) (hb : d149558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148357, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148357, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148358 q = 1) (hb : d149559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148358, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148358, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148359 q = 1) (hb : d149560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148359, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148359, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148360 q = 1) (hb : d149561 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148360, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148360, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148361 q = 1) (hb : d149640 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148361, d149640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28303 q ha hb
    | true =>
      simp only [d148361, d149640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148362 q = 1) (hb : d149641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148362, d149641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148362, d149641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148363 q = 1) (hb : d149642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148363, d149642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148363, d149642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148364 q = 1) (hb : d149643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148364, d149643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148364, d149643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148365 q = 1) (hb : d149644 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148365, d149644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148365, d149644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148366 q = 1) (hb : d149645 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148366, d149645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148366, d149645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro28329 (p : Pattern) (ha : d148372 p = 1) (hb : d149651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148361 q = 1) (hb : d149640 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148361, d149640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28303 q ha hb
    | true =>
      simp only [d148361, d149640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148362 q = 1) (hb : d149641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148362, d149641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148362, d149641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148363 q = 1) (hb : d149642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148363, d149642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148363, d149642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148364 q = 1) (hb : d149643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148364, d149643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148364, d149643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148365 q = 1) (hb : d149644 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148365, d149644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148365, d149644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148367 q = 1) (hb : d149646 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148367, d149646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28306 q ha hb
    | true =>
      simp only [d148367, d149646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148368 q = 1) (hb : d149647 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148368, d149647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148368, d149647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148369 q = 1) (hb : d149648 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148369, d149648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148369, d149648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148370 q = 1) (hb : d149649 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148370, d149649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148370, d149649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148371 q = 1) (hb : d149650 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148371, d149650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148371, d149650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148372 q = 1) (hb : d149651 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148372, d149651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148372, d149651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro28330 (p : Pattern) (ha : d148379 p = 1) (hb : d149658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148346 q = 1) (hb : d149630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148346, d149630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28324 q ha hb
    | true =>
      simp only [d148346, d149630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28325 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148259 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148347 q = 1) (hb : d149631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148347, d149631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148347, d149631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d148349 q = 1) (hb : d149633 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148349, d149633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28326 q ha hb
    | true =>
      simp only [d148349, d149633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148350 q = 1) (hb : d149634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148350, d149634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148350, d149634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148351 q = 1) (hb : d149635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148351, d149635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148351, d149635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148377 q = 1) (hb : d149656 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148377, d149656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148377, d149656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148378 q = 1) (hb : d149657 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148378, d149657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148378, d149657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148379 q = 1) (hb : d149658 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148379, d149658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148379, d149658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro28331 (p : Pattern) (ha : d148381 p = 1) (hb : d149660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148367 q = 1) (hb : d149646 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148367, d149646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28306 q ha hb
    | true =>
      simp only [d148367, d149646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148368 q = 1) (hb : d149647 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148368, d149647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148368, d149647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148369 q = 1) (hb : d149648 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148369, d149648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148369, d149648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148370 q = 1) (hb : d149649 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148370, d149649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148370, d149649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148371 q = 1) (hb : d149650 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148371, d149650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148371, d149650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148381 q = 1) (hb : d149660 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148381, d149660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148381, d149660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28332 (p : Pattern) (ha : d148388 p = 1) (hb : d149666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17369 q = 1) (hb : d128031 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
  have h2 (q : Pattern) (ha : d10343 q = 1) (hb : d101664 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
    | true =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17370 q = 1) (hb : d128032 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, d128032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17370, d128032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10345 q = 1) (hb : d101666 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17371 q = 1) (hb : d128033 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17371, d128033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17371, d128033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17372 q = 1) (hb : d128034 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17372, d128034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17372, d128034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22930 q = 1) (hb : d148387 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22930, d148387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22930, d148387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d128036 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d148388 q = 1) (hb : d149666 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148388, d149666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d148388, d149666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro28333 (p : Pattern) (ha : d148390 p = 1) (hb : d149670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17369 q = 1) (hb : d128031 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
  have h2 (q : Pattern) (ha : d10343 q = 1) (hb : d101664 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
    | true =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17370 q = 1) (hb : d128032 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, d128032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17370, d128032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10345 q = 1) (hb : d101666 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17371 q = 1) (hb : d128033 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17371, d128033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17371, d128033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17372 q = 1) (hb : d128034 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17372, d128034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17372, d128034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17376 q = 1) (hb : d128038 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
  have h8 (q : Pattern) (ha : d10364 q = 1) (hb : d101685 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
    | true =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17377 q = 1) (hb : d128039 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d128039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17377, d128039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10366 q = 1) (hb : d101687 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17378 q = 1) (hb : d128040 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d128040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17378, d128040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17379 q = 1) (hb : d128041 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17379, d128041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17379, d128041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22932 q = 1) (hb : d148389 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22932, d148389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22932, d148389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113973 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148390 q = 1) (hb : d149670 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148390, d149670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d148390, d149670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro28334 (p : Pattern) (ha : d148405 p = 1) (hb : d149675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17376 q = 1) (hb : d128038 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
  have h2 (q : Pattern) (ha : d10364 q = 1) (hb : d101685 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
    | true =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17377 q = 1) (hb : d128039 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d128039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17377, d128039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10366 q = 1) (hb : d101687 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17378 q = 1) (hb : d128040 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d128040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17378, d128040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17379 q = 1) (hb : d128041 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17379, d128041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17379, d128041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22943 q = 1) (hb : d148400 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22943, d148400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22943, d148400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28298 q ha hb
  have h8 (q : Pattern) (ha : d22688 q = 1) (hb : d148206 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d148206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28298 q ha hb
    | true =>
      simp only [d22688, d148206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22944 q = 1) (hb : d148401 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22944, d148401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22944, d148401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22689 q = 1) (hb : d148207 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d148207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22689, d148207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22945 q = 1) (hb : d148402 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22945, d148402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22945, d148402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22946 q = 1) (hb : d148403 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22946, d148403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22946, d148403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22947 q = 1) (hb : d148404 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22947, d148404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22947, d148404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148394 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148405 q = 1) (hb : d149675 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148405, d149675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d148405, d149675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro28335 (p : Pattern) (ha : d148420 p = 1) (hb : d149681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148390 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148391 q = 1) (hb : d149667 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148391, d149667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28332 q ha hb
    | true =>
      simp only [d148391, d149667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d148392 q = 1) (hb : d149668 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148392, d149668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148392, d149668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148393 q = 1) (hb : d149669 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148393, d149669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148393, d149669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148395 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148396 q = 1) (hb : d149671 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148396, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28333 q ha hb
    | true =>
      simp only [d148396, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148397 q = 1) (hb : d149672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148397, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148397, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148398 q = 1) (hb : d149673 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148398, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148398, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148399 q = 1) (hb : d149674 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148399, d149674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148399, d149674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148405 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d148406 q = 1) (hb : d149671 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148406, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28333 q ha hb
    | true =>
      simp only [d148406, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d148407 q = 1) (hb : d149672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148407, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148407, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148408 q = 1) (hb : d149673 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148408, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148408, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148415 q = 1) (hb : d149676 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148415, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28334 q ha hb
    | true =>
      simp only [d148415, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148416 q = 1) (hb : d149677 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148416, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148416, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148417 q = 1) (hb : d149678 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148417, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148417, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148418 q = 1) (hb : d149679 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148418, d149679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148418, d149679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d148419 q = 1) (hb : d149680 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148419, d149680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148419, d149680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d148420 q = 1) (hb : d149681 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148420, d149681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d148420, d149681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro28336 (p : Pattern) (ha : d148425 p = 1) (hb : d149686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148405 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148406 q = 1) (hb : d149671 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148406, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28333 q ha hb
    | true =>
      simp only [d148406, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d148407 q = 1) (hb : d149672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148407, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148407, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148408 q = 1) (hb : d149673 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148408, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148408, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148414 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148415 q = 1) (hb : d149676 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148415, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28334 q ha hb
    | true =>
      simp only [d148415, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148416 q = 1) (hb : d149677 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148416, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148416, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148417 q = 1) (hb : d149678 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148417, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148417, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148418 q = 1) (hb : d149679 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148418, d149679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148418, d149679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148423 q = 1) (hb : d149684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148423, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148423, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d148424 q = 1) (hb : d149685 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148424, d149685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148424, d149685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d148425 q = 1) (hb : d149686 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148425, d149686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148425, d149686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro28337 (p : Pattern) (ha : d148431 p = 1) (hb : d149692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148421 q = 1) (hb : d149682 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148421, d149682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28335 q ha hb
    | true =>
      simp only [d148421, d149682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148422 q = 1) (hb : d149683 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148422, d149683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148422, d149683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148426 q = 1) (hb : d149687 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148426, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28336 q ha hb
    | true =>
      simp only [d148426, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148427 q = 1) (hb : d149688 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148427, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148427, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148428 q = 1) (hb : d149689 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148428, d149689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148428, d149689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148429 q = 1) (hb : d149690 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148429, d149690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148429, d149690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148430 q = 1) (hb : d149691 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148430, d149691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148430, d149691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148431 q = 1) (hb : d149692 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148431, d149692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148431, d149692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28338 (p : Pattern) (ha : d148439 p = 1) (hb : d149694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148433 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148434 q = 1) (hb : d149676 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148434, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28334 q ha hb
    | true =>
      simp only [d148434, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d148435 q = 1) (hb : d149677 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148435, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148435, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148436 q = 1) (hb : d149678 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148436, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148436, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148437 q = 1) (hb : d149684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148437, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148437, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148438 q = 1) (hb : d149693 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148438, d149693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148438, d149693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148439 q = 1) (hb : d149694 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148439, d149694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148439, d149694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro28339 (p : Pattern) (ha : d148445 p = 1) (hb : d149700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148426 q = 1) (hb : d149687 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148426, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28336 q ha hb
    | true =>
      simp only [d148426, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148427 q = 1) (hb : d149688 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148427, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148427, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148440 q = 1) (hb : d149695 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148440, d149695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28338 q ha hb
    | true =>
      simp only [d148440, d149695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148441 q = 1) (hb : d149696 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148441, d149696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148441, d149696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148442 q = 1) (hb : d149697 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148442, d149697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148442, d149697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148443 q = 1) (hb : d149698 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148443, d149698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148443, d149698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148444 q = 1) (hb : d149699 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148444, d149699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148444, d149699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148445 q = 1) (hb : d149700 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148445, d149700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148445, d149700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28340 (p : Pattern) (ha : d148467 p = 1) (hb : d149686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148405 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148406 q = 1) (hb : d149671 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148406, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28333 q ha hb
    | true =>
      simp only [d148406, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d148407 q = 1) (hb : d149672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148407, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148407, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148408 q = 1) (hb : d149673 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148408, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148408, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148414 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148415 q = 1) (hb : d149676 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148415, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28334 q ha hb
    | true =>
      simp only [d148415, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148416 q = 1) (hb : d149677 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148416, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148416, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148417 q = 1) (hb : d149678 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148417, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148417, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148418 q = 1) (hb : d149679 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148418, d149679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148418, d149679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148461 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d148462 q = 1) (hb : d149676 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148462, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28334 q ha hb
    | true =>
      simp only [d148462, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d148463 q = 1) (hb : d149677 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148463, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148463, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148464 q = 1) (hb : d149678 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148464, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148464, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148465 q = 1) (hb : d149684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148465, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148465, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d148466 q = 1) (hb : d149685 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148466, d149685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148466, d149685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148467 q = 1) (hb : d149686 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148467, d149686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148467, d149686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro28341 (p : Pattern) (ha : d148473 p = 1) (hb : d149706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148468 q = 1) (hb : d149687 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148468, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28340 q ha hb
    | true =>
      simp only [d148468, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148469 q = 1) (hb : d149688 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148469, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148469, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148470 q = 1) (hb : d149703 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148470, d149703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148470, d149703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148471 q = 1) (hb : d149704 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148471, d149704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148471, d149704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148472 q = 1) (hb : d149705 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148472, d149705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148472, d149705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148473 q = 1) (hb : d149706 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148473, d149706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148473, d149706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28342 (p : Pattern) (ha : d148479 p = 1) (hb : d149712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148446 q = 1) (hb : d149701 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148446, d149701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28337 q ha hb
    | true =>
      simp only [d148446, d149701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28339 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148459 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148460 q = 1) (hb : d149702 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148460, d149702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148460, d149702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d148474 q = 1) (hb : d149707 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148474, d149707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28341 q ha hb
    | true =>
      simp only [d148474, d149707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148475 q = 1) (hb : d149708 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148475, d149708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148475, d149708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148476 q = 1) (hb : d149709 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148476, d149709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148476, d149709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148477 q = 1) (hb : d149710 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148477, d149710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148477, d149710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148478 q = 1) (hb : d149711 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148478, d149711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148478, d149711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148479 q = 1) (hb : d149712 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148479, d149712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148479, d149712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro28343 (p : Pattern) (ha : d148458 p = 1) (hb : d149717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148440 q = 1) (hb : d149695 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148440, d149695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28338 q ha hb
    | true =>
      simp only [d148440, d149695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148441 q = 1) (hb : d149696 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148441, d149696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148441, d149696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148455 q = 1) (hb : d149714 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148455, d149714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148455, d149714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148456 q = 1) (hb : d149715 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148456, d149715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148456, d149715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148457 q = 1) (hb : d149716 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148457, d149716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148457, d149716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148458 q = 1) (hb : d149717 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148458, d149717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148458, d149717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28344 (p : Pattern) (ha : d148486 p = 1) (hb : d149723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148481 q = 1) (hb : d149718 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148481, d149718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28343 q ha hb
    | true =>
      simp only [d148481, d149718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148482 q = 1) (hb : d149719 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148482, d149719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148482, d149719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148483 q = 1) (hb : d149720 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148483, d149720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148483, d149720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148484 q = 1) (hb : d149721 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148484, d149721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148484, d149721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148485 q = 1) (hb : d149722 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148485, d149722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148485, d149722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148486 q = 1) (hb : d149723 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148486, d149723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148486, d149723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28345 (p : Pattern) (ha : d148492 p = 1) (hb : d149729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148255 q = 1) (hb : d149563 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148255, d149563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148255, d149563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28304 q ha hb
  have h2 (q : Pattern) (ha : d148256 q = 1) (hb : d149564 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148256, d149564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148256, d149564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148265 q = 1) (hb : d149573 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148265, d149573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28304 q ha hb
    | true =>
      simp only [d148265, d149573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28307 q ha hb
  have h4 (q : Pattern) (ha : d148266 q = 1) (hb : d149574 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148266, d149574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148266, d149574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148267 q = 1) (hb : d149575 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148267, d149575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148267, d149575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148355 q = 1) (hb : d149639 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148355, d149639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28319 q ha hb
    | true =>
      simp only [d148355, d149639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28327 q ha hb
  have h7 (q : Pattern) (ha : d148373 q = 1) (hb : d149652 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148373, d149652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28328 q ha hb
    | true =>
      simp only [d148373, d149652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28329 q ha hb
  have h8 (q : Pattern) (ha : d148374 q = 1) (hb : d149653 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148374, d149653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148374, d149653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148375 q = 1) (hb : d149654 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148375, d149654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148375, d149654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d148376 q = 1) (hb : d149655 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148376, d149655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148376, d149655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148380 q = 1) (hb : d149659 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148380, d149659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148380, d149659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28330 q ha hb
  have h12 (q : Pattern) (ha : d148382 q = 1) (hb : d149661 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148382, d149661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148382, d149661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28331 q ha hb
  have h13 (q : Pattern) (ha : d148383 q = 1) (hb : d149662 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148383, d149662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148383, d149662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148384 q = 1) (hb : d149663 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148384, d149663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148384, d149663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d148385 q = 1) (hb : d149664 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148385, d149664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d148385, d149664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d148386 q = 1) (hb : d149665 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148386, d149665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148386, d149665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148480 q = 1) (hb : d149713 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148480, d149713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148480, d149713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28342 q ha hb
  have h18 (q : Pattern) (ha : d148487 q = 1) (hb : d149724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148487, d149724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148487, d149724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28344 q ha hb
  have h19 (q : Pattern) (ha : d148488 q = 1) (hb : d149725 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148488, d149725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148488, d149725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d148489 q = 1) (hb : d149726 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148489, d149726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d148489, d149726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d148490 q = 1) (hb : d149727 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148490, d149727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d148490, d149727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d148491 q = 1) (hb : d149728 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148491, d149728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d148491, d149728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d148492 q = 1) (hb : d149729 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d148492, d149729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d148492, d149729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro28346 (p : Pattern) (ha : d148498 p = 1) (hb : d149735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148493 q = 1) (hb : d149730 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d148493, d149730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148493, d149730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28345 q ha hb
  have h2 (q : Pattern) (ha : d148494 q = 1) (hb : d149731 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d148494, d149731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148494, d149731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148495 q = 1) (hb : d149732 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d148495, d149732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148495, d149732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148496 q = 1) (hb : d149733 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d148496, d149733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148496, d149733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148497 q = 1) (hb : d149734 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d148497, d149734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148497, d149734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148498 q = 1) (hb : d149735 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d148498, d149735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148498, d149735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28347 (p : Pattern) (ha : d148504 p = 1) (hb : d149741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d147261 q = 1) (hb : d148924 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147261, d148924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28105 q ha hb
    | true =>
      simp only [d147261, d148924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28146 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147500 q = 1) (hb : d149112 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147500, d149112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147500, d149112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28191 q ha hb
  have h3 (q : Pattern) (ha : d147501 q = 1) (hb : d149113 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d147501, d149113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147501, d149113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147858 q = 1) (hb : d149319 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147858, d149319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147858, d149319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28244 q ha hb
  have h5 (q : Pattern) (ha : d147859 q = 1) (hb : d149320 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d147859, d149320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147859, d149320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147860 q = 1) (hb : d149321 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d147860, d149321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147860, d149321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148199 q = 1) (hb : d149527 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d148199, d149527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148199, d149527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28296 q ha hb
  have h8 (q : Pattern) (ha : d148200 q = 1) (hb : d149528 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d148200, d149528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148200, d149528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148201 q = 1) (hb : d149529 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d148201, d149529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148201, d149529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148202 q = 1) (hb : d149530 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d148202, d149530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148202, d149530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148499 q = 1) (hb : d149736 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d148499, d149736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148499, d149736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28346 q ha hb
  have h12 (q : Pattern) (ha : d148500 q = 1) (hb : d149737 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d148500, d149737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148500, d149737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148501 q = 1) (hb : d149738 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d148501, d149738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148501, d149738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148502 q = 1) (hb : d149739 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d148502, d149739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148502, d149739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148503 q = 1) (hb : d149740 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d148503, d149740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148503, d149740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148504 q = 1) (hb : d149741 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d148504, d149741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148504, d149741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro28348 (p : Pattern) (ha : d148510 p = 1) (hb : d149747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148505 q = 1) (hb : d149742 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d148505, d149742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28347 q ha hb
    | true =>
      simp only [d148505, d149742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148506 q = 1) (hb : d149743 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d148506, d149743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148506, d149743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148507 q = 1) (hb : d149744 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d148507, d149744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148507, d149744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148508 q = 1) (hb : d149745 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d148508, d149745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148508, d149745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148509 q = 1) (hb : d149746 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d148509, d149746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148509, d149746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148510 q = 1) (hb : d149747 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d148510, d149747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148510, d149747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28349 (p : Pattern) (ha : d148516 p = 1) (hb : d149753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148511 q = 1) (hb : d149748 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d148511, d149748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28348 q ha hb
    | true =>
      simp only [d148511, d149748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148512 q = 1) (hb : d149749 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d148512, d149749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148512, d149749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148513 q = 1) (hb : d149750 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d148513, d149750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148513, d149750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148514 q = 1) (hb : d149751 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d148514, d149751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148514, d149751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148515 q = 1) (hb : d149752 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d148515, d149752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148515, d149752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148516 q = 1) (hb : d149753 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d148516, d149753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148516, d149753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28350 (p : Pattern) (ha : d148522 p = 1) (hb : d149759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148517 q = 1) (hb : d149754 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d148517, d149754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28349 q ha hb
    | true =>
      simp only [d148517, d149754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148518 q = 1) (hb : d149755 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d148518, d149755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148518, d149755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148519 q = 1) (hb : d149756 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d148519, d149756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148519, d149756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148520 q = 1) (hb : d149757 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d148520, d149757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148520, d149757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148521 q = 1) (hb : d149758 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d148521, d149758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148521, d149758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148522 q = 1) (hb : d149759 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d148522, d149759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148522, d149759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28351 (p : Pattern) (ha : d148528 p = 1) (hb : d149765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148523 q = 1) (hb : d149760 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d148523, d149760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28350 q ha hb
    | true =>
      simp only [d148523, d149760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148524 q = 1) (hb : d149761 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d148524, d149761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148524, d149761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148525 q = 1) (hb : d149762 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d148525, d149762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148525, d149762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148526 q = 1) (hb : d149763 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d148526, d149763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148526, d149763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148527 q = 1) (hb : d149764 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d148527, d149764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148527, d149764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148528 q = 1) (hb : d149765 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d148528, d149765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148528, d149765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28352 (p : Pattern) (ha : d148534 p = 1) (hb : d149771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148529 q = 1) (hb : d149766 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d148529, d149766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28351 q ha hb
    | true =>
      simp only [d148529, d149766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148530 q = 1) (hb : d149767 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d148530, d149767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148530, d149767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148531 q = 1) (hb : d149768 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d148531, d149768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148531, d149768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148532 q = 1) (hb : d149769 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d148532, d149769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148532, d149769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148533 q = 1) (hb : d149770 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d148533, d149770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148533, d149770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148534 q = 1) (hb : d149771 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d148534, d149771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148534, d149771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28353 (p : Pattern) (ha : d148540 p = 1) (hb : d149777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148535 q = 1) (hb : d149772 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d148535, d149772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28352 q ha hb
    | true =>
      simp only [d148535, d149772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148536 q = 1) (hb : d149773 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d148536, d149773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148536, d149773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148537 q = 1) (hb : d149774 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d148537, d149774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148537, d149774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148538 q = 1) (hb : d149775 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d148538, d149775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148538, d149775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148539 q = 1) (hb : d149776 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d148539, d149776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148539, d149776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148540 q = 1) (hb : d149777 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d148540, d149777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148540, d149777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28354 (p : Pattern) (ha : d148546 p = 1) (hb : d149783 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148541 q = 1) (hb : d149778 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d148541, d149778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28353 q ha hb
    | true =>
      simp only [d148541, d149778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148542 q = 1) (hb : d149779 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d148542, d149779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148542, d149779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148543 q = 1) (hb : d149780 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d148543, d149780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148543, d149780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148544 q = 1) (hb : d149781 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d148544, d149781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148544, d149781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148545 q = 1) (hb : d149782 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d148545, d149782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148545, d149782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148546 q = 1) (hb : d149783 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d148546, d149783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148546, d149783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28355 (p : Pattern) (ha : d109112 p = 1) (hb : d146837 p = 1) : d149786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d146837 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10668 q = 1) (hb : d146837 q = 1) : d148567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27795 q ha hb
    | true =>
      simp only [d10668, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10722 q = 1) (hb : d146837 q = 1) : d148622 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10722, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10722, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10723 q = 1) (hb : d146837 q = 1) : d148623 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10723, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10723, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10724 q = 1) (hb : d146837 q = 1) : d148624 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10724, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10724, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10725 q = 1) (hb : d146837 q = 1) : d148625 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10725, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10725, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109112 q = 1) (hb : d146837 q = 1) : d149786 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109112, d149786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109112, d149786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28356 (p : Pattern) (ha : d109122 p = 1) (hb : d146837 p = 1) : d149796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d146837 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10698 q = 1) (hb : d146837 q = 1) : d148598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10698, d148598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27800 q ha hb
    | true =>
      simp only [d10698, d148598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109118 q = 1) (hb : d146837 q = 1) : d149792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109118, d149792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109118, d149792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109119 q = 1) (hb : d146837 q = 1) : d149793 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109119, d149793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109119, d149793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109120 q = 1) (hb : d146837 q = 1) : d149794 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109120, d149794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109120, d149794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109121 q = 1) (hb : d146837 q = 1) : d149795 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109121, d149795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109121, d149795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109122 q = 1) (hb : d146837 q = 1) : d149796 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109122, d149796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109122, d149796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28357 (p : Pattern) (ha : d109128 p = 1) (hb : d146837 p = 1) : d149802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10727 q = 1) (hb : d146837 q = 1) : d148627 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10727, d148627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27803 q ha hb
    | true =>
      simp only [d10727, d148627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27804 q ha hb
  have h2 (q : Pattern) (ha : d10728 q = 1) (hb : d146837 q = 1) : d148628 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10728, d148628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10728, d148628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109110 q = 1) (hb : d146837 q = 1) : d149784 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109110, d149784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109110, d149784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109111 q = 1) (hb : d146837 q = 1) : d149785 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109111, d149785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109111, d149785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109113 q = 1) (hb : d146837 q = 1) : d149787 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109113, d149787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109113, d149787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28355 q ha hb
  have h6 (q : Pattern) (ha : d109114 q = 1) (hb : d146837 q = 1) : d149788 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109114, d149788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109114, d149788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d109115 q = 1) (hb : d146837 q = 1) : d149789 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109115, d149789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109115, d149789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d109116 q = 1) (hb : d146837 q = 1) : d149790 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109116, d149790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109116, d149790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109117 q = 1) (hb : d146837 q = 1) : d149791 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109117, d149791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109117, d149791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109123 q = 1) (hb : d146837 q = 1) : d149797 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109123, d149797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109123, d149797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28356 q ha hb
  have h11 (q : Pattern) (ha : d109124 q = 1) (hb : d146837 q = 1) : d149798 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109124, d149798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109124, d149798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109125 q = 1) (hb : d146837 q = 1) : d149799 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109125, d149799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109125, d149799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d109126 q = 1) (hb : d146837 q = 1) : d149800 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109126, d149800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109126, d149800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109127 q = 1) (hb : d146837 q = 1) : d149801 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109127, d149801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109127, d149801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109128 q = 1) (hb : d146837 q = 1) : d149802 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109128, d149802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109128, d149802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro28358 (p : Pattern) (ha : d109134 p = 1) (hb : d146837 p = 1) : d149808 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d146837 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d109129 q = 1) (hb : d146837 q = 1) : d149803 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109129, d149803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109129, d149803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28357 q ha hb
  have h3 (q : Pattern) (ha : d109130 q = 1) (hb : d146837 q = 1) : d149804 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109130, d149804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109130, d149804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109131 q = 1) (hb : d146837 q = 1) : d149805 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109131, d149805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109131, d149805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109132 q = 1) (hb : d146837 q = 1) : d149806 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109132, d149806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109132, d149806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109133 q = 1) (hb : d146837 q = 1) : d149807 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109133, d149807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109133, d149807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109134 q = 1) (hb : d146837 q = 1) : d149808 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109134, d149808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109134, d149808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28359 (p : Pattern) (ha : d109137 p = 1) (hb : d146837 p = 1) : d149811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10890 q = 1) (hb : d146837 q = 1) : d148764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10890, d148764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27831 q ha hb
    | true =>
      simp only [d10890, d148764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27832 q ha hb
  have h2 (q : Pattern) (ha : d10891 q = 1) (hb : d146837 q = 1) : d148765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10891, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10891, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10892 q = 1) (hb : d146837 q = 1) : d148766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10892, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10892, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10893 q = 1) (hb : d146837 q = 1) : d148767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10893, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10893, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10894 q = 1) (hb : d146837 q = 1) : d148768 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10894, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10894, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109137 q = 1) (hb : d146837 q = 1) : d149811 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109137, d149811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109137, d149811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28360 (p : Pattern) (ha : d109148 p = 1) (hb : d146837 p = 1) : d149822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109143 q = 1) (hb : d146837 q = 1) : d149817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109143, d149817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27861 q ha hb
    | true =>
      simp only [d109143, d149817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27838 q ha hb
  have h2 (q : Pattern) (ha : d109144 q = 1) (hb : d146837 q = 1) : d149818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109144, d149818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109144, d149818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109145 q = 1) (hb : d146837 q = 1) : d149819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109145, d149819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109145, d149819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109146 q = 1) (hb : d146837 q = 1) : d149820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109146, d149820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109146, d149820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109147 q = 1) (hb : d146837 q = 1) : d149821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109147, d149821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109147, d149821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109148 q = 1) (hb : d146837 q = 1) : d149822 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109148, d149822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109148, d149822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28361 (p : Pattern) (ha : d109154 p = 1) (hb : d146837 p = 1) : d149828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10896 q = 1) (hb : d146837 q = 1) : d148770 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10896, d148770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27830 q ha hb
    | true =>
      simp only [d10896, d148770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27833 q ha hb
  have h2 (q : Pattern) (ha : d10897 q = 1) (hb : d146837 q = 1) : d148771 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10897, d148771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10897, d148771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109135 q = 1) (hb : d146837 q = 1) : d149809 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109135, d149809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109135, d149809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109136 q = 1) (hb : d146837 q = 1) : d149810 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109136, d149810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109136, d149810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109138 q = 1) (hb : d146837 q = 1) : d149812 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109138, d149812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109138, d149812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28359 q ha hb
  have h6 (q : Pattern) (ha : d109139 q = 1) (hb : d146837 q = 1) : d149813 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109139, d149813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109139, d149813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d109140 q = 1) (hb : d146837 q = 1) : d149814 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109140, d149814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109140, d149814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d109141 q = 1) (hb : d146837 q = 1) : d149815 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109141, d149815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109141, d149815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109142 q = 1) (hb : d146837 q = 1) : d149816 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109142, d149816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109142, d149816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109149 q = 1) (hb : d146837 q = 1) : d149823 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109149, d149823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109149, d149823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28360 q ha hb
  have h11 (q : Pattern) (ha : d109150 q = 1) (hb : d146837 q = 1) : d149824 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109150, d149824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109150, d149824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109151 q = 1) (hb : d146837 q = 1) : d149825 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109151, d149825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109151, d149825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d109152 q = 1) (hb : d146837 q = 1) : d149826 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109152, d149826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109152, d149826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109153 q = 1) (hb : d146837 q = 1) : d149827 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109153, d149827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109153, d149827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109154 q = 1) (hb : d146837 q = 1) : d149828 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109154, d149828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109154, d149828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro28362 (p : Pattern) (ha : d109160 p = 1) (hb : d146837 p = 1) : d149834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109155 q = 1) (hb : d146837 q = 1) : d149829 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109155, d149829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109155, d149829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28361 q ha hb
  have h2 (q : Pattern) (ha : d109156 q = 1) (hb : d146837 q = 1) : d149830 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109156, d149830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109156, d149830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109157 q = 1) (hb : d146837 q = 1) : d149831 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109157, d149831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109157, d149831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109158 q = 1) (hb : d146837 q = 1) : d149832 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109158, d149832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109158, d149832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109159 q = 1) (hb : d146837 q = 1) : d149833 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109159, d149833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109159, d149833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109160 q = 1) (hb : d146837 q = 1) : d149834 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109160, d149834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109160, d149834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28363 (p : Pattern) (ha : d109164 p = 1) (hb : d146837 p = 1) : d149838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11130 q = 1) (hb : d146837 q = 1) : d148952 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11130, d148952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27873 q ha hb
    | true =>
      simp only [d11130, d148952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27874 q ha hb
  have h2 (q : Pattern) (ha : d11131 q = 1) (hb : d146837 q = 1) : d148953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11131, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11131, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11132 q = 1) (hb : d146837 q = 1) : d148954 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11132, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11132, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11133 q = 1) (hb : d146837 q = 1) : d148955 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11133, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11133, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11134 q = 1) (hb : d146837 q = 1) : d148956 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11134, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11134, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109164 q = 1) (hb : d146837 q = 1) : d149838 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109164, d149838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109164, d149838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28364 (p : Pattern) (ha : d109175 p = 1) (hb : d146837 p = 1) : d149849 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109170 q = 1) (hb : d146837 q = 1) : d149844 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109170, d149844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27908 q ha hb
    | true =>
      simp only [d109170, d149844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27881 q ha hb
  have h2 (q : Pattern) (ha : d109171 q = 1) (hb : d146837 q = 1) : d149845 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109171, d149845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109171, d149845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109172 q = 1) (hb : d146837 q = 1) : d149846 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109172, d149846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109172, d149846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109173 q = 1) (hb : d146837 q = 1) : d149847 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109173, d149847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109173, d149847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109174 q = 1) (hb : d146837 q = 1) : d149848 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109174, d149848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109174, d149848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109175 q = 1) (hb : d146837 q = 1) : d149849 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109175, d149849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109175, d149849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28365 (p : Pattern) (ha : d109181 p = 1) (hb : d146837 p = 1) : d149855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11136 q = 1) (hb : d146837 q = 1) : d148958 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11136, d148958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27872 q ha hb
    | true =>
      simp only [d11136, d148958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27875 q ha hb
  have h2 (q : Pattern) (ha : d11137 q = 1) (hb : d146837 q = 1) : d148959 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11137, d148959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11137, d148959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109162 q = 1) (hb : d146837 q = 1) : d149836 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109162, d149836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109162, d149836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109163 q = 1) (hb : d146837 q = 1) : d149837 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109163, d149837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109163, d149837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109165 q = 1) (hb : d146837 q = 1) : d149839 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109165, d149839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109165, d149839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28363 q ha hb
  have h6 (q : Pattern) (ha : d109166 q = 1) (hb : d146837 q = 1) : d149840 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109166, d149840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109166, d149840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d109167 q = 1) (hb : d146837 q = 1) : d149841 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109167, d149841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109167, d149841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d109168 q = 1) (hb : d146837 q = 1) : d149842 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109168, d149842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109168, d149842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109169 q = 1) (hb : d146837 q = 1) : d149843 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109169, d149843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109169, d149843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109176 q = 1) (hb : d146837 q = 1) : d149850 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109176, d149850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109176, d149850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28364 q ha hb
  have h11 (q : Pattern) (ha : d109177 q = 1) (hb : d146837 q = 1) : d149851 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109177, d149851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109177, d149851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109178 q = 1) (hb : d146837 q = 1) : d149852 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109178, d149852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109178, d149852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d109179 q = 1) (hb : d146837 q = 1) : d149853 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109179, d149853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109179, d149853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109180 q = 1) (hb : d146837 q = 1) : d149854 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109180, d149854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109180, d149854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109181 q = 1) (hb : d146837 q = 1) : d149855 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109181, d149855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109181, d149855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro28366 (p : Pattern) (ha : d109187 p = 1) (hb : d146837 p = 1) : d149861 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109182 q = 1) (hb : d146837 q = 1) : d149856 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109182, d149856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109182, d149856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28365 q ha hb
  have h2 (q : Pattern) (ha : d109183 q = 1) (hb : d146837 q = 1) : d149857 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109183, d149857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109183, d149857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109184 q = 1) (hb : d146837 q = 1) : d149858 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109184, d149858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109184, d149858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109185 q = 1) (hb : d146837 q = 1) : d149859 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109185, d149859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109185, d149859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109186 q = 1) (hb : d146837 q = 1) : d149860 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109186, d149860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109186, d149860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109187 q = 1) (hb : d146837 q = 1) : d149861 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109187, d149861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109187, d149861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28367 (p : Pattern) (ha : d109192 p = 1) (hb : d146837 p = 1) : d149866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11400 q = 1) (hb : d146837 q = 1) : d149150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11400, d149150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27922 q ha hb
    | true =>
      simp only [d11400, d149150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27923 q ha hb
  have h2 (q : Pattern) (ha : d11401 q = 1) (hb : d146837 q = 1) : d149151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11401, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11401, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11402 q = 1) (hb : d146837 q = 1) : d149152 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11402, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11402, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11403 q = 1) (hb : d146837 q = 1) : d149153 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11403, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11403, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11404 q = 1) (hb : d146837 q = 1) : d149154 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11404, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11404, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109192 q = 1) (hb : d146837 q = 1) : d149866 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109192, d149866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109192, d149866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28368 (p : Pattern) (ha : d109203 p = 1) (hb : d146837 p = 1) : d149877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109198 q = 1) (hb : d146837 q = 1) : d149872 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109198, d149872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27957 q ha hb
    | true =>
      simp only [d109198, d149872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27930 q ha hb
  have h2 (q : Pattern) (ha : d109199 q = 1) (hb : d146837 q = 1) : d149873 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109199, d149873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109199, d149873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109200 q = 1) (hb : d146837 q = 1) : d149874 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109200, d149874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109200, d149874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109201 q = 1) (hb : d146837 q = 1) : d149875 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109201, d149875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109201, d149875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109202 q = 1) (hb : d146837 q = 1) : d149876 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109202, d149876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109202, d149876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109203 q = 1) (hb : d146837 q = 1) : d149877 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109203, d149877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109203, d149877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28369 (p : Pattern) (ha : d109209 p = 1) (hb : d146837 p = 1) : d149883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11406 q = 1) (hb : d146837 q = 1) : d149156 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11406, d149156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27921 q ha hb
    | true =>
      simp only [d11406, d149156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27924 q ha hb
  have h2 (q : Pattern) (ha : d11407 q = 1) (hb : d146837 q = 1) : d149157 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11407, d149157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11407, d149157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109190 q = 1) (hb : d146837 q = 1) : d149864 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109190, d149864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109190, d149864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109191 q = 1) (hb : d146837 q = 1) : d149865 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109191, d149865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109191, d149865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109193 q = 1) (hb : d146837 q = 1) : d149867 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109193, d149867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109193, d149867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28367 q ha hb
  have h6 (q : Pattern) (ha : d109194 q = 1) (hb : d146837 q = 1) : d149868 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109194, d149868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109194, d149868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d109195 q = 1) (hb : d146837 q = 1) : d149869 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109195, d149869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109195, d149869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d109196 q = 1) (hb : d146837 q = 1) : d149870 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109196, d149870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109196, d149870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109197 q = 1) (hb : d146837 q = 1) : d149871 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109197, d149871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109197, d149871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109204 q = 1) (hb : d146837 q = 1) : d149878 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109204, d149878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109204, d149878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28368 q ha hb
  have h11 (q : Pattern) (ha : d109205 q = 1) (hb : d146837 q = 1) : d149879 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109205, d149879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109205, d149879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109206 q = 1) (hb : d146837 q = 1) : d149880 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109206, d149880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109206, d149880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d109207 q = 1) (hb : d146837 q = 1) : d149881 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109207, d149881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109207, d149881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109208 q = 1) (hb : d146837 q = 1) : d149882 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109208, d149882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109208, d149882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109209 q = 1) (hb : d146837 q = 1) : d149883 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109209, d149883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109209, d149883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro28370 (p : Pattern) (ha : d109215 p = 1) (hb : d146837 p = 1) : d149889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109210 q = 1) (hb : d146837 q = 1) : d149884 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109210, d149884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109210, d149884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28369 q ha hb
  have h2 (q : Pattern) (ha : d109211 q = 1) (hb : d146837 q = 1) : d149885 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109211, d149885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109211, d149885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109212 q = 1) (hb : d146837 q = 1) : d149886 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109212, d149886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109212, d149886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109213 q = 1) (hb : d146837 q = 1) : d149887 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109213, d149887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109213, d149887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109214 q = 1) (hb : d146837 q = 1) : d149888 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109214, d149888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109214, d149888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109215 q = 1) (hb : d146837 q = 1) : d149889 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109215, d149889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109215, d149889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28371 (p : Pattern) (ha : d109221 p = 1) (hb : d146837 p = 1) : d149895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11671 q = 1) (hb : d146837 q = 1) : d149358 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11671, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27971 q ha hb
    | true =>
      simp only [d11671, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27972 q ha hb
  have h2 (q : Pattern) (ha : d11672 q = 1) (hb : d146837 q = 1) : d149359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11672, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11672, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11673 q = 1) (hb : d146837 q = 1) : d149360 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11673, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11673, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11674 q = 1) (hb : d146837 q = 1) : d149361 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11674, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11674, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11675 q = 1) (hb : d146837 q = 1) : d149362 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11675, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11675, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109221 q = 1) (hb : d146837 q = 1) : d149895 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109221, d149895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109221, d149895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28372 (p : Pattern) (ha : d109232 p = 1) (hb : d146837 p = 1) : d149906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109227 q = 1) (hb : d146837 q = 1) : d149901 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109227, d149901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28006 q ha hb
    | true =>
      simp only [d109227, d149901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27979 q ha hb
  have h2 (q : Pattern) (ha : d109228 q = 1) (hb : d146837 q = 1) : d149902 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109228, d149902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109228, d149902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109229 q = 1) (hb : d146837 q = 1) : d149903 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109229, d149903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109229, d149903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109230 q = 1) (hb : d146837 q = 1) : d149904 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109230, d149904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109230, d149904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109231 q = 1) (hb : d146837 q = 1) : d149905 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109231, d149905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109231, d149905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109232 q = 1) (hb : d146837 q = 1) : d149906 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109232, d149906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109232, d149906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28373 (p : Pattern) (ha : d109238 p = 1) (hb : d146837 p = 1) : d149912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11677 q = 1) (hb : d146837 q = 1) : d149364 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11677, d149364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27970 q ha hb
    | true =>
      simp only [d11677, d149364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27973 q ha hb
  have h2 (q : Pattern) (ha : d11678 q = 1) (hb : d146837 q = 1) : d149365 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11678, d149365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11678, d149365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109219 q = 1) (hb : d146837 q = 1) : d149893 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109219, d149893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109219, d149893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109220 q = 1) (hb : d146837 q = 1) : d149894 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109220, d149894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109220, d149894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109222 q = 1) (hb : d146837 q = 1) : d149896 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109222, d149896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109222, d149896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28371 q ha hb
  have h6 (q : Pattern) (ha : d109223 q = 1) (hb : d146837 q = 1) : d149897 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109223, d149897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109223, d149897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d109224 q = 1) (hb : d146837 q = 1) : d149898 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109224, d149898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109224, d149898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d109225 q = 1) (hb : d146837 q = 1) : d149899 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109225, d149899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109225, d149899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109226 q = 1) (hb : d146837 q = 1) : d149900 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109226, d149900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109226, d149900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109233 q = 1) (hb : d146837 q = 1) : d149907 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109233, d149907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109233, d149907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28372 q ha hb
  have h11 (q : Pattern) (ha : d109234 q = 1) (hb : d146837 q = 1) : d149908 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109234, d149908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109234, d149908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109235 q = 1) (hb : d146837 q = 1) : d149909 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109235, d149909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109235, d149909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d109236 q = 1) (hb : d146837 q = 1) : d149910 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109236, d149910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109236, d149910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109237 q = 1) (hb : d146837 q = 1) : d149911 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109237, d149911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109237, d149911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109238 q = 1) (hb : d146837 q = 1) : d149912 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109238, d149912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109238, d149912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro28374 (p : Pattern) (ha : d109244 p = 1) (hb : d146837 p = 1) : d149918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109239 q = 1) (hb : d146837 q = 1) : d149913 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109239, d149913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109239, d149913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28373 q ha hb
  have h2 (q : Pattern) (ha : d109240 q = 1) (hb : d146837 q = 1) : d149914 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109240, d149914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109240, d149914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109241 q = 1) (hb : d146837 q = 1) : d149915 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109241, d149915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109241, d149915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109242 q = 1) (hb : d146837 q = 1) : d149916 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109242, d149916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109242, d149916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109243 q = 1) (hb : d146837 q = 1) : d149917 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109243, d149917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109243, d149917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109244 q = 1) (hb : d146837 q = 1) : d149918 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109244, d149918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109244, d149918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28375 (p : Pattern) (ha : d109251 p = 1) (hb : d146837 p = 1) : d149925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11943 q = 1) (hb : d146837 q = 1) : d149567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11943, d149567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28020 q ha hb
    | true =>
      simp only [d11943, d149567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28021 q ha hb
  have h2 (q : Pattern) (ha : d11944 q = 1) (hb : d146837 q = 1) : d149568 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11944, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11944, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11945 q = 1) (hb : d146837 q = 1) : d149569 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11945, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11945, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11946 q = 1) (hb : d146837 q = 1) : d149570 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11946, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11946, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11947 q = 1) (hb : d146837 q = 1) : d149571 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11947, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11947, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109251 q = 1) (hb : d146837 q = 1) : d149925 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109251, d149925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109251, d149925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28376 (p : Pattern) (ha : d109262 p = 1) (hb : d146837 p = 1) : d149936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109257 q = 1) (hb : d146837 q = 1) : d149931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109257, d149931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28055 q ha hb
    | true =>
      simp only [d109257, d149931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28028 q ha hb
  have h2 (q : Pattern) (ha : d109258 q = 1) (hb : d146837 q = 1) : d149932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109258, d149932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109258, d149932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109259 q = 1) (hb : d146837 q = 1) : d149933 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109259, d149933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109259, d149933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109260 q = 1) (hb : d146837 q = 1) : d149934 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109260, d149934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109260, d149934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109261 q = 1) (hb : d146837 q = 1) : d149935 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109261, d149935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109261, d149935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109262 q = 1) (hb : d146837 q = 1) : d149936 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109262, d149936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109262, d149936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28377 (p : Pattern) (ha : d109268 p = 1) (hb : d146837 p = 1) : d149942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11949 q = 1) (hb : d146837 q = 1) : d149573 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11949, d149573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28019 q ha hb
    | true =>
      simp only [d11949, d149573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28022 q ha hb
  have h2 (q : Pattern) (ha : d11950 q = 1) (hb : d146837 q = 1) : d149574 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11950, d149574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11950, d149574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109249 q = 1) (hb : d146837 q = 1) : d149923 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109249, d149923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109249, d149923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109250 q = 1) (hb : d146837 q = 1) : d149924 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109250, d149924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109250, d149924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109252 q = 1) (hb : d146837 q = 1) : d149926 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109252, d149926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109252, d149926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28375 q ha hb
  have h6 (q : Pattern) (ha : d109253 q = 1) (hb : d146837 q = 1) : d149927 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109253, d149927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109253, d149927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d109254 q = 1) (hb : d146837 q = 1) : d149928 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109254, d149928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109254, d149928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d109255 q = 1) (hb : d146837 q = 1) : d149929 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109255, d149929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109255, d149929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109256 q = 1) (hb : d146837 q = 1) : d149930 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109256, d149930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109256, d149930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109263 q = 1) (hb : d146837 q = 1) : d149937 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109263, d149937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109263, d149937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28376 q ha hb
  have h11 (q : Pattern) (ha : d109264 q = 1) (hb : d146837 q = 1) : d149938 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109264, d149938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109264, d149938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109265 q = 1) (hb : d146837 q = 1) : d149939 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109265, d149939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109265, d149939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d109266 q = 1) (hb : d146837 q = 1) : d149940 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109266, d149940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109266, d149940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109267 q = 1) (hb : d146837 q = 1) : d149941 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109267, d149941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109267, d149941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109268 q = 1) (hb : d146837 q = 1) : d149942 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109268, d149942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109268, d149942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro28378 (p : Pattern) (ha : d109274 p = 1) (hb : d146837 p = 1) : d149948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109269 q = 1) (hb : d146837 q = 1) : d149943 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109269, d149943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109269, d149943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28377 q ha hb
  have h2 (q : Pattern) (ha : d109270 q = 1) (hb : d146837 q = 1) : d149944 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109270, d149944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109270, d149944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109271 q = 1) (hb : d146837 q = 1) : d149945 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109271, d149945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109271, d149945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109272 q = 1) (hb : d146837 q = 1) : d149946 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109272, d149946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109272, d149946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109273 q = 1) (hb : d146837 q = 1) : d149947 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109273, d149947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109273, d149947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109274 q = 1) (hb : d146837 q = 1) : d149948 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109274, d149948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109274, d149948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28379 (p : Pattern) (ha : d109280 p = 1) (hb : d146837 p = 1) : d149954 p = 1 := by
  have h0 (q : Pattern) (ha : d109161 q = 1) (hb : d146837 q = 1) : d149835 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109161, d149835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28358 q ha hb
    | true =>
      simp only [d109161, d149835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28362 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d109188 q = 1) (hb : d146837 q = 1) : d149862 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109188, d149862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109188, d149862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28366 q ha hb
  have h3 (q : Pattern) (ha : d109189 q = 1) (hb : d146837 q = 1) : d149863 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109189, d149863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109189, d149863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109216 q = 1) (hb : d146837 q = 1) : d149890 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109216, d149890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109216, d149890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28370 q ha hb
  have h5 (q : Pattern) (ha : d109217 q = 1) (hb : d146837 q = 1) : d149891 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109217, d149891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109217, d149891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109218 q = 1) (hb : d146837 q = 1) : d149892 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109218, d149892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109218, d149892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109245 q = 1) (hb : d146837 q = 1) : d149919 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109245, d149919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109245, d149919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28374 q ha hb
  have h8 (q : Pattern) (ha : d109246 q = 1) (hb : d146837 q = 1) : d149920 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109246, d149920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109246, d149920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109247 q = 1) (hb : d146837 q = 1) : d149921 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109247, d149921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109247, d149921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109248 q = 1) (hb : d146837 q = 1) : d149922 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109248, d149922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109248, d149922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109275 q = 1) (hb : d146837 q = 1) : d149949 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109275, d149949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109275, d149949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28378 q ha hb
  have h12 (q : Pattern) (ha : d109276 q = 1) (hb : d146837 q = 1) : d149950 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109276, d149950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109276, d149950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109277 q = 1) (hb : d146837 q = 1) : d149951 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109277, d149951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109277, d149951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109278 q = 1) (hb : d146837 q = 1) : d149952 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109278, d149952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109278, d149952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d109279 q = 1) (hb : d146837 q = 1) : d149953 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d109279, d149953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109279, d149953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109280 q = 1) (hb : d146837 q = 1) : d149954 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d109280, d149954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109280, d149954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro28380 (p : Pattern) (ha : d109286 p = 1) (hb : d146837 p = 1) : d149960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109281 q = 1) (hb : d146837 q = 1) : d149955 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d109281, d149955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28379 q ha hb
    | true =>
      simp only [d109281, d149955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109282 q = 1) (hb : d146837 q = 1) : d149956 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d109282, d149956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109282, d149956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109283 q = 1) (hb : d146837 q = 1) : d149957 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d109283, d149957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109283, d149957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109284 q = 1) (hb : d146837 q = 1) : d149958 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d109284, d149958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109284, d149958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109285 q = 1) (hb : d146837 q = 1) : d149959 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d109285, d149959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109285, d149959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109286 q = 1) (hb : d146837 q = 1) : d149960 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d109286, d149960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109286, d149960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28381 (p : Pattern) (ha : d109292 p = 1) (hb : d146837 p = 1) : d149966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109287 q = 1) (hb : d146837 q = 1) : d149961 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d109287, d149961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28380 q ha hb
    | true =>
      simp only [d109287, d149961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109288 q = 1) (hb : d146837 q = 1) : d149962 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d109288, d149962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109288, d149962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109289 q = 1) (hb : d146837 q = 1) : d149963 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d109289, d149963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109289, d149963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109290 q = 1) (hb : d146837 q = 1) : d149964 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d109290, d149964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109290, d149964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109291 q = 1) (hb : d146837 q = 1) : d149965 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d109291, d149965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109291, d149965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109292 q = 1) (hb : d146837 q = 1) : d149966 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d109292, d149966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109292, d149966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28382 (p : Pattern) (ha : d109298 p = 1) (hb : d146837 p = 1) : d149972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109293 q = 1) (hb : d146837 q = 1) : d149967 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d109293, d149967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28381 q ha hb
    | true =>
      simp only [d109293, d149967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109294 q = 1) (hb : d146837 q = 1) : d149968 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d109294, d149968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109294, d149968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109295 q = 1) (hb : d146837 q = 1) : d149969 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d109295, d149969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109295, d149969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109296 q = 1) (hb : d146837 q = 1) : d149970 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d109296, d149970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109296, d149970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109297 q = 1) (hb : d146837 q = 1) : d149971 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d109297, d149971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109297, d149971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109298 q = 1) (hb : d146837 q = 1) : d149972 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d109298, d149972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109298, d149972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28383 (p : Pattern) (ha : d109304 p = 1) (hb : d146837 p = 1) : d149978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109299 q = 1) (hb : d146837 q = 1) : d149973 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d109299, d149973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28382 q ha hb
    | true =>
      simp only [d109299, d149973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109300 q = 1) (hb : d146837 q = 1) : d149974 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d109300, d149974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109300, d149974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109301 q = 1) (hb : d146837 q = 1) : d149975 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d109301, d149975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109301, d149975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109302 q = 1) (hb : d146837 q = 1) : d149976 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d109302, d149976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109302, d149976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109303 q = 1) (hb : d146837 q = 1) : d149977 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d109303, d149977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109303, d149977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109304 q = 1) (hb : d146837 q = 1) : d149978 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d109304, d149978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109304, d149978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28384 (p : Pattern) (ha : d109310 p = 1) (hb : d146837 p = 1) : d149984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109305 q = 1) (hb : d146837 q = 1) : d149979 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d109305, d149979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28383 q ha hb
    | true =>
      simp only [d109305, d149979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109306 q = 1) (hb : d146837 q = 1) : d149980 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d109306, d149980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109306, d149980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109307 q = 1) (hb : d146837 q = 1) : d149981 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d109307, d149981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109307, d149981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109308 q = 1) (hb : d146837 q = 1) : d149982 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d109308, d149982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109308, d149982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109309 q = 1) (hb : d146837 q = 1) : d149983 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d109309, d149983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109309, d149983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109310 q = 1) (hb : d146837 q = 1) : d149984 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d109310, d149984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109310, d149984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28385 (p : Pattern) (ha : d109316 p = 1) (hb : d146837 p = 1) : d149990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109311 q = 1) (hb : d146837 q = 1) : d149985 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d109311, d149985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28384 q ha hb
    | true =>
      simp only [d109311, d149985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109312 q = 1) (hb : d146837 q = 1) : d149986 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d109312, d149986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109312, d149986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109313 q = 1) (hb : d146837 q = 1) : d149987 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d109313, d149987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109313, d149987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109314 q = 1) (hb : d146837 q = 1) : d149988 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d109314, d149988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109314, d149988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109315 q = 1) (hb : d146837 q = 1) : d149989 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d109315, d149989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109315, d149989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109316 q = 1) (hb : d146837 q = 1) : d149990 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d109316, d149990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109316, d149990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28386 (p : Pattern) (ha : d109322 p = 1) (hb : d146837 p = 1) : d149996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109317 q = 1) (hb : d146837 q = 1) : d149991 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d109317, d149991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28385 q ha hb
    | true =>
      simp only [d109317, d149991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109318 q = 1) (hb : d146837 q = 1) : d149992 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d109318, d149992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109318, d149992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109319 q = 1) (hb : d146837 q = 1) : d149993 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d109319, d149993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109319, d149993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109320 q = 1) (hb : d146837 q = 1) : d149994 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d109320, d149994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109320, d149994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109321 q = 1) (hb : d146837 q = 1) : d149995 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d109321, d149995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109321, d149995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109322 q = 1) (hb : d146837 q = 1) : d149996 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d109322, d149996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109322, d149996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28387 (p : Pattern) (ha : d104 p = 1) (hb : d146857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d146852 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d146853 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d146853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d146853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d146854 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d146854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d146854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d146855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d146855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d146855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d146856 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d146856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d146856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d146857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d146857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d146857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro28388 (p : Pattern) (ha : d111 p = 1) (hb : d146864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146852 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d146853 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d146853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d146853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d146854 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d146854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d146854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d146855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d146855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d146855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d146856 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d146856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d146856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d146859 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d107 q = 1) (hb : d146860 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d146860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107, d146860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d108 q = 1) (hb : d146861 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d146861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108, d146861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109 q = 1) (hb : d146862 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d146862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109, d146862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d110 q = 1) (hb : d146863 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d146863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d110, d146863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d111 q = 1) (hb : d146864 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d146864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d111, d146864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro28389 (p : Pattern) (ha : d406 p = 1) (hb : d146871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146859 q = 1) : d0 q = 1 := by
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
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d146860 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d146860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d146860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d146861 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d146861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d146861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d146869 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d146869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d146869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d146870 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d146870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d146870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d146871 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d146871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d146871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28390 (p : Pattern) (ha : d462 p = 1) (hb : d146896 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146891 q = 1) : d0 q = 1 := by
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
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d146892 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d146892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d146892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d146893 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d146893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d146893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d146894 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d146894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d146894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d146895 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d146895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d146895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d146896 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d146896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d146896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28391 (p : Pattern) (ha : d53647 p = 1) (hb : d146902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d146865 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d146865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28387 q ha hb
    | true =>
      simp only [d112, d146865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28388 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d146866 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d146866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d146866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d146867 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d146867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d146867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d146868 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d146868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d146868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d146872 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d146872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d146872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28389 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d146873 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d146873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d146873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d146874 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d146874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d146874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d146875 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d146875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d146875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d146876 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d146876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d146876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d146897 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d146897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d146897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28390 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d146898 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d146898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d146898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d146899 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d146899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d146899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d146900 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d146900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d146900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d146901 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d146901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d146901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d146902 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d146902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d146902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro28392 (p : Pattern) (ha : d146966 p = 1) (hb : d148619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146928 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d146955 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d146852 q = 1) (hb : d148560 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28072 q ha hb
    | true =>
      simp only [d146852, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d146956 q = 1) (hb : d148615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146956, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d146956, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d146962 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d146963 q = 1) (hb : d148616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146963, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146963, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d146964 q = 1) (hb : d148617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146964, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d146964, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146965 q = 1) (hb : d148618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146965, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d146965, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146966 q = 1) (hb : d148619 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146966, d148619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146966, d148619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro28393 (p : Pattern) (ha : d146985 p = 1) (hb : d148626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146928 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146934 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146955 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146852 q = 1) (hb : d148560 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28072 q ha hb
    | true =>
      simp only [d146852, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d146956 q = 1) (hb : d148615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146956, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d146956, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d146962 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d146963 q = 1) (hb : d148616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146963, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146963, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d146964 q = 1) (hb : d148617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146964, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d146964, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146965 q = 1) (hb : d148618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146965, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146965, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d146971 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d146975 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d146977 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d146859 q = 1) (hb : d148567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146859, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28074 q ha hb
    | true =>
      simp only [d146859, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d146978 q = 1) (hb : d148622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146978, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d146978, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d146981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d146982 q = 1) (hb : d148623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146982, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d146982, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d146983 q = 1) (hb : d148624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146983, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d146983, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d146984 q = 1) (hb : d148625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146984, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d146984, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d146985 q = 1) (hb : d148626 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146985, d148626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d146985, d148626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro28394 (p : Pattern) (ha : d146994 p = 1) (hb : d149786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146977 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146859 q = 1) (hb : d148567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146859, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28074 q ha hb
    | true =>
      simp only [d146859, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d146978 q = 1) (hb : d148622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146978, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d146978, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d146981 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146982 q = 1) (hb : d148623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146982, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146982, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146992 q = 1) (hb : d148624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146992, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146992, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146993 q = 1) (hb : d148625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146993, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146993, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146994 q = 1) (hb : d149786 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146994, d149786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146994, d149786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28395 (p : Pattern) (ha : d147030 p = 1) (hb : d149796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147019 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146891 q = 1) (hb : d148598 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146891, d148598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28079 q ha hb
    | true =>
      simp only [d146891, d148598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d147020 q = 1) (hb : d149792 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147020, d149792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147020, d149792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147026 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147027 q = 1) (hb : d149793 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147027, d149793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147027, d149793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147028 q = 1) (hb : d149794 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147028, d149794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147028, d149794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147029 q = 1) (hb : d149795 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147029, d149795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147029, d149795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147030 q = 1) (hb : d149796 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147030, d149796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147030, d149796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28396 (p : Pattern) (ha : d147036 p = 1) (hb : d149802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146922 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146986 q = 1) (hb : d148627 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146986, d148627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28392 q ha hb
    | true =>
      simp only [d146986, d148627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28393 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146988 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146989 q = 1) (hb : d148628 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146989, d148628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146989, d148628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146990 q = 1) (hb : d149784 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146990, d149784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146990, d149784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146991 q = 1) (hb : d149785 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146991, d149785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146991, d149785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146995 q = 1) (hb : d149787 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146995, d149787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d146995, d149787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28394 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d146996 q = 1) (hb : d149788 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146996, d149788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146996, d149788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d146997 q = 1) (hb : d149789 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146997, d149789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d146997, d149789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d146998 q = 1) (hb : d149790 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146998, d149790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146998, d149790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d146999 q = 1) (hb : d149791 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146999, d149791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146999, d149791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147031 q = 1) (hb : d149797 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147031, d149797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147031, d149797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28395 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147032 q = 1) (hb : d149798 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147032, d149798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147032, d149798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147033 q = 1) (hb : d149799 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147033, d149799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147033, d149799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147034 q = 1) (hb : d149800 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147034, d149800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147034, d149800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147035 q = 1) (hb : d149801 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147035, d149801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147035, d149801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147036 q = 1) (hb : d149802 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147036, d149802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147036, d149802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro28397 (p : Pattern) (ha : d147042 p = 1) (hb : d149808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d146903 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d146903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d146903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28391 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d146904 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d146904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d146904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d146905 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d146905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d146905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d146906 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d146906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d146906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d146907 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d146907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d146907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147037 q = 1) (hb : d149803 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147037, d149803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147037, d149803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28396 q ha hb
  have h8 (q : Pattern) (ha : d147038 q = 1) (hb : d149804 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147038, d149804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147038, d149804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147039 q = 1) (hb : d149805 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147039, d149805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147039, d149805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147040 q = 1) (hb : d149806 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147040, d149806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147040, d149806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147041 q = 1) (hb : d149807 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147041, d149807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147041, d149807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d147042 q = 1) (hb : d149808 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147042, d149808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d147042, d149808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro28398 (p : Pattern) (ha : d147136 p = 1) (hb : d148759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147095 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147125 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147060 q = 1) (hb : d148754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147060, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28108 q ha hb
    | true =>
      simp only [d147060, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28109 q ha hb
  have h5 (q : Pattern) (ha : d147126 q = 1) (hb : d148755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147126, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147126, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d147132 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d147133 q = 1) (hb : d148756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147133, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147133, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d147134 q = 1) (hb : d148757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147134, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147134, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147135 q = 1) (hb : d148758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147135, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147135, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147136 q = 1) (hb : d148759 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147136, d148759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147136, d148759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro28399 (p : Pattern) (ha : d147157 p = 1) (hb : d148769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147086 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147125 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147060 q = 1) (hb : d148754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147060, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28108 q ha hb
    | true =>
      simp only [d147060, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28109 q ha hb
  have h4 (q : Pattern) (ha : d147126 q = 1) (hb : d148755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147126, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147126, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147132 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147133 q = 1) (hb : d148756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147133, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147133, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d147134 q = 1) (hb : d148757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147134, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147134, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147135 q = 1) (hb : d148758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147135, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147135, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147142 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147147 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d147149 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147070 q = 1) (hb : d148764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147070, d148764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28111 q ha hb
    | true =>
      simp only [d147070, d148764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28112 q ha hb
  have h13 (q : Pattern) (ha : d147150 q = 1) (hb : d148765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147150, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d147150, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147153 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147154 q = 1) (hb : d148766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147154, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147154, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147155 q = 1) (hb : d148767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147155, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147155, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147156 q = 1) (hb : d148768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147156, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147156, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147157 q = 1) (hb : d148769 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147157, d148769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147157, d148769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro28400 (p : Pattern) (ha : d147177 p = 1) (hb : d149811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147149 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147070 q = 1) (hb : d148764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147070, d148764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28111 q ha hb
    | true =>
      simp only [d147070, d148764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28112 q ha hb
  have h3 (q : Pattern) (ha : d147150 q = 1) (hb : d148765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147150, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147150, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147153 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147154 q = 1) (hb : d148766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147154, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147154, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147175 q = 1) (hb : d148767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147175, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147175, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147176 q = 1) (hb : d148768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147176, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147176, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147177 q = 1) (hb : d149811 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147177, d149811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147177, d149811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28401 (p : Pattern) (ha : d147241 p = 1) (hb : d149822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147225 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147230 q = 1) (hb : d149817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147230, d149817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28140 q ha hb
    | true =>
      simp only [d147230, d149817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28143 q ha hb
  have h3 (q : Pattern) (ha : d147231 q = 1) (hb : d149818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147231, d149818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147231, d149818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147237 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147238 q = 1) (hb : d149819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147238, d149819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147238, d149819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147239 q = 1) (hb : d149820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147239, d149820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147239, d149820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147240 q = 1) (hb : d149821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147240, d149821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147240, d149821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147241 q = 1) (hb : d149822 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147241, d149822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147241, d149822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28402 (p : Pattern) (ha : d147254 p = 1) (hb : d149828 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147078 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147158 q = 1) (hb : d148770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147158, d148770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28398 q ha hb
    | true =>
      simp only [d147158, d148770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28399 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147171 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147172 q = 1) (hb : d148771 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147172, d148771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147172, d148771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147173 q = 1) (hb : d149809 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147173, d149809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147173, d149809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147174 q = 1) (hb : d149810 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147174, d149810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147174, d149810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147178 q = 1) (hb : d149812 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147178, d149812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147178, d149812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28400 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d147180 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d147181 q = 1) (hb : d149813 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147181, d149813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147181, d149813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d147182 q = 1) (hb : d149814 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147182, d149814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147182, d149814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d147183 q = 1) (hb : d149815 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147183, d149815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147183, d149815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d147184 q = 1) (hb : d149816 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147184, d149816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147184, d149816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147242 q = 1) (hb : d149823 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147242, d149823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147242, d149823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28401 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147249 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147250 q = 1) (hb : d149824 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147250, d149824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147250, d149824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147251 q = 1) (hb : d149825 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147251, d149825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147251, d149825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147252 q = 1) (hb : d149826 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147252, d149826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147252, d149826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147253 q = 1) (hb : d149827 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147253, d149827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147253, d149827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147254 q = 1) (hb : d149828 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147254, d149828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147254, d149828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro28403 (p : Pattern) (ha : d147260 p = 1) (hb : d149834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147255 q = 1) (hb : d149829 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147255, d149829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147255, d149829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28402 q ha hb
  have h2 (q : Pattern) (ha : d147256 q = 1) (hb : d149830 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147256, d149830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147256, d149830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147257 q = 1) (hb : d149831 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147257, d149831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147257, d149831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147258 q = 1) (hb : d149832 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147258, d149832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147258, d149832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147259 q = 1) (hb : d149833 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147259, d149833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147259, d149833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147260 q = 1) (hb : d149834 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147260, d149834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147260, d149834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28404 (p : Pattern) (ha : d147365 p = 1) (hb : d148947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147315 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147324 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147354 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147289 q = 1) (hb : d148942 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147289, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28151 q ha hb
    | true =>
      simp only [d147289, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28152 q ha hb
  have h5 (q : Pattern) (ha : d147355 q = 1) (hb : d148943 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147355, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147355, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d147361 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d147362 q = 1) (hb : d148944 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147362, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147362, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d147363 q = 1) (hb : d148945 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147363, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147363, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147364 q = 1) (hb : d148946 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147364, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147364, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147365 q = 1) (hb : d148947 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147365, d148947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147365, d148947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro28405 (p : Pattern) (ha : d147386 p = 1) (hb : d148957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147324 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147354 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147289 q = 1) (hb : d148942 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147289, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28151 q ha hb
    | true =>
      simp only [d147289, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28152 q ha hb
  have h4 (q : Pattern) (ha : d147355 q = 1) (hb : d148943 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147355, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147355, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147361 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147362 q = 1) (hb : d148944 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147362, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147362, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d147363 q = 1) (hb : d148945 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147363, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147363, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147364 q = 1) (hb : d148946 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147364, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147364, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147371 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147376 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d147378 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147299 q = 1) (hb : d148952 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147299, d148952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28154 q ha hb
    | true =>
      simp only [d147299, d148952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28155 q ha hb
  have h13 (q : Pattern) (ha : d147379 q = 1) (hb : d148953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147379, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d147379, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147382 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147383 q = 1) (hb : d148954 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147383, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147383, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147384 q = 1) (hb : d148955 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147384, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147384, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147385 q = 1) (hb : d148956 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147385, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147385, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147386 q = 1) (hb : d148957 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147386, d148957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147386, d148957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro28406 (p : Pattern) (ha : d147406 p = 1) (hb : d149838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147378 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147299 q = 1) (hb : d148952 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147299, d148952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28154 q ha hb
    | true =>
      simp only [d147299, d148952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28155 q ha hb
  have h3 (q : Pattern) (ha : d147379 q = 1) (hb : d148953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147379, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147379, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147382 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147383 q = 1) (hb : d148954 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147383, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147383, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147404 q = 1) (hb : d148955 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147404, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147404, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147405 q = 1) (hb : d148956 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147405, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147405, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147406 q = 1) (hb : d149838 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147406, d149838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147406, d149838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28407 (p : Pattern) (ha : d147480 p = 1) (hb : d149849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147464 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147469 q = 1) (hb : d149844 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147469, d149844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28185 q ha hb
    | true =>
      simp only [d147469, d149844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28188 q ha hb
  have h3 (q : Pattern) (ha : d147470 q = 1) (hb : d149845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147470, d149845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147470, d149845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147476 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147477 q = 1) (hb : d149846 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147477, d149846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147477, d149846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147478 q = 1) (hb : d149847 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147478, d149847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147478, d149847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147479 q = 1) (hb : d149848 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147479, d149848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147479, d149848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147480 q = 1) (hb : d149849 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147480, d149849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147480, d149849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28408 (p : Pattern) (ha : d147493 p = 1) (hb : d149855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147387 q = 1) (hb : d148958 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147387, d148958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28404 q ha hb
    | true =>
      simp only [d147387, d148958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28405 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147400 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147401 q = 1) (hb : d148959 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147401, d148959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147401, d148959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147402 q = 1) (hb : d149836 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147402, d149836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147402, d149836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147403 q = 1) (hb : d149837 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147403, d149837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147403, d149837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147407 q = 1) (hb : d149839 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147407, d149839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147407, d149839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28406 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d147409 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d147410 q = 1) (hb : d149840 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147410, d149840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147410, d149840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d147411 q = 1) (hb : d149841 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147411, d149841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147411, d149841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d147412 q = 1) (hb : d149842 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147412, d149842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147412, d149842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d147413 q = 1) (hb : d149843 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147413, d149843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147413, d149843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147481 q = 1) (hb : d149850 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147481, d149850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147481, d149850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28407 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147488 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147489 q = 1) (hb : d149851 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147489, d149851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147489, d149851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147490 q = 1) (hb : d149852 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147490, d149852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147490, d149852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147491 q = 1) (hb : d149853 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147491, d149853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147491, d149853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147492 q = 1) (hb : d149854 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147492, d149854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147492, d149854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147493 q = 1) (hb : d149855 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147493, d149855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147493, d149855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro28409 (p : Pattern) (ha : d147499 p = 1) (hb : d149861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147494 q = 1) (hb : d149856 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147494, d149856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147494, d149856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28408 q ha hb
  have h2 (q : Pattern) (ha : d147495 q = 1) (hb : d149857 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147495, d149857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147495, d149857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147496 q = 1) (hb : d149858 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147496, d149858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147496, d149858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147497 q = 1) (hb : d149859 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147497, d149859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147497, d149859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147498 q = 1) (hb : d149860 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147498, d149860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147498, d149860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147499 q = 1) (hb : d149861 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147499, d149861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147499, d149861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28410 (p : Pattern) (ha : d147664 p = 1) (hb : d149145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147590 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147599 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147644 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147564 q = 1) (hb : d149140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147564, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28199 q ha hb
    | true =>
      simp only [d147564, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28200 q ha hb
  have h5 (q : Pattern) (ha : d147645 q = 1) (hb : d149141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147645, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147645, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d147660 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d147661 q = 1) (hb : d149142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147661, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147661, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d147662 q = 1) (hb : d149143 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147662, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147662, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147663 q = 1) (hb : d149144 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147663, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147663, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147664 q = 1) (hb : d149145 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147664, d149145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147664, d149145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro28411 (p : Pattern) (ha : d147686 p = 1) (hb : d149155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147590 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147599 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147644 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147564 q = 1) (hb : d149140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147564, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28199 q ha hb
    | true =>
      simp only [d147564, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28200 q ha hb
  have h4 (q : Pattern) (ha : d147645 q = 1) (hb : d149141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147645, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147645, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147660 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147661 q = 1) (hb : d149142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147661, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147661, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d147662 q = 1) (hb : d149143 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147662, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147662, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147663 q = 1) (hb : d149144 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147663, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147663, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147670 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147675 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d147678 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147574 q = 1) (hb : d149150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147574, d149150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28202 q ha hb
    | true =>
      simp only [d147574, d149150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28203 q ha hb
  have h13 (q : Pattern) (ha : d147679 q = 1) (hb : d149151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147679, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d147679, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147682 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147683 q = 1) (hb : d149152 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147683, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147683, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147684 q = 1) (hb : d149153 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147684, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147684, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147685 q = 1) (hb : d149154 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147685, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147685, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147686 q = 1) (hb : d149155 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147686, d149155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147686, d149155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro28412 (p : Pattern) (ha : d147711 p = 1) (hb : d149866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147678 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147574 q = 1) (hb : d149150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147574, d149150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28202 q ha hb
    | true =>
      simp only [d147574, d149150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28203 q ha hb
  have h3 (q : Pattern) (ha : d147679 q = 1) (hb : d149151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147679, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147679, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147682 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147683 q = 1) (hb : d149152 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147683, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147683, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147709 q = 1) (hb : d149153 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147709, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147709, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147710 q = 1) (hb : d149154 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147710, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147710, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147711 q = 1) (hb : d149866 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147711, d149866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147711, d149866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28413 (p : Pattern) (ha : d147807 p = 1) (hb : d149269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147764 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147765 q = 1) (hb : d149254 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147765, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28231 q ha hb
    | true =>
      simp only [d147765, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d147766 q = 1) (hb : d149255 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147766, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147766, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147767 q = 1) (hb : d149256 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147767, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147767, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147773 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147774 q = 1) (hb : d149259 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147774, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28232 q ha hb
    | true =>
      simp only [d147774, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d147775 q = 1) (hb : d149260 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147775, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147775, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147776 q = 1) (hb : d149261 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147776, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147776, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147777 q = 1) (hb : d149262 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147777, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147777, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147792 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d147793 q = 1) (hb : d149259 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147793, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28232 q ha hb
    | true =>
      simp only [d147793, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d147794 q = 1) (hb : d149260 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147794, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147794, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147795 q = 1) (hb : d149261 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147795, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147795, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147796 q = 1) (hb : d149267 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147796, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147796, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d147806 q = 1) (hb : d149268 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147806, d149268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147806, d149268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147807 q = 1) (hb : d149269 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147807, d149269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147807, d149269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro28414 (p : Pattern) (ha : d147813 p = 1) (hb : d149283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147808 q = 1) (hb : d149270 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147808, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28413 q ha hb
    | true =>
      simp only [d147808, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147809 q = 1) (hb : d149271 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147809, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147809, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147799 q = 1) (hb : d149278 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147799, d149278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28236 q ha hb
    | true =>
      simp only [d147799, d149278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147800 q = 1) (hb : d149279 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147800, d149279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147800, d149279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147810 q = 1) (hb : d149280 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147810, d149280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147810, d149280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147811 q = 1) (hb : d149281 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147811, d149281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147811, d149281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147812 q = 1) (hb : d149282 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147812, d149282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147812, d149282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147813 q = 1) (hb : d149283 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147813, d149283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147813, d149283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28415 (p : Pattern) (ha : d147838 p = 1) (hb : d149877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147805 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147818 q = 1) (hb : d149872 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147818, d149872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28414 q ha hb
    | true =>
      simp only [d147818, d149872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28241 q ha hb
  have h3 (q : Pattern) (ha : d147819 q = 1) (hb : d149873 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147819, d149873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147819, d149873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147834 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147835 q = 1) (hb : d149874 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147835, d149874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147835, d149874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147836 q = 1) (hb : d149875 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147836, d149875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147836, d149875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147837 q = 1) (hb : d149876 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147837, d149876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147837, d149876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147838 q = 1) (hb : d149877 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147838, d149877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147838, d149877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28416 (p : Pattern) (ha : d147851 p = 1) (hb : d149883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147687 q = 1) (hb : d149156 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147687, d149156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28410 q ha hb
    | true =>
      simp only [d147687, d149156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28411 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147705 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147706 q = 1) (hb : d149157 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147706, d149157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147706, d149157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147707 q = 1) (hb : d149864 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147707, d149864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147707, d149864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147708 q = 1) (hb : d149865 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147708, d149865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147708, d149865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147712 q = 1) (hb : d149867 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147712, d149867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147712, d149867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28412 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d147714 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d147715 q = 1) (hb : d149868 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147715, d149868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147715, d149868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d147716 q = 1) (hb : d149869 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147716, d149869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147716, d149869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d147717 q = 1) (hb : d149870 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147717, d149870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147717, d149870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d147718 q = 1) (hb : d149871 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147718, d149871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147718, d149871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147839 q = 1) (hb : d149878 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147839, d149878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147839, d149878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28415 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147846 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147847 q = 1) (hb : d149879 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147847, d149879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147847, d149879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147848 q = 1) (hb : d149880 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147848, d149880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147848, d149880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147849 q = 1) (hb : d149881 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147849, d149881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147849, d149881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147850 q = 1) (hb : d149882 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147850, d149882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147850, d149882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147851 q = 1) (hb : d149883 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147851, d149883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147851, d149883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro28417 (p : Pattern) (ha : d147857 p = 1) (hb : d149889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147852 q = 1) (hb : d149884 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147852, d149884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147852, d149884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28416 q ha hb
  have h2 (q : Pattern) (ha : d147853 q = 1) (hb : d149885 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147853, d149885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147853, d149885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147854 q = 1) (hb : d149886 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147854, d149886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147854, d149886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147855 q = 1) (hb : d149887 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147855, d149887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147855, d149887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147856 q = 1) (hb : d149888 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147856, d149888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147856, d149888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147857 q = 1) (hb : d149889 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147857, d149889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147857, d149889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28418 (p : Pattern) (ha : d148013 p = 1) (hb : d149353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147944 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147953 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147993 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147918 q = 1) (hb : d149348 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147918, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28251 q ha hb
    | true =>
      simp only [d147918, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28252 q ha hb
  have h5 (q : Pattern) (ha : d147994 q = 1) (hb : d149349 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147994, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147994, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d148009 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d148010 q = 1) (hb : d149350 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148010, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148010, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d148011 q = 1) (hb : d149351 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148011, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d148011, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148012 q = 1) (hb : d149352 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148012, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148012, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148013 q = 1) (hb : d149353 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148013, d149353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148013, d149353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro28419 (p : Pattern) (ha : d148035 p = 1) (hb : d149363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147944 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147953 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147993 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147918 q = 1) (hb : d149348 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147918, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28251 q ha hb
    | true =>
      simp only [d147918, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28252 q ha hb
  have h4 (q : Pattern) (ha : d147994 q = 1) (hb : d149349 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147994, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147994, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148009 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148010 q = 1) (hb : d149350 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148010, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148010, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148011 q = 1) (hb : d149351 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148011, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148011, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148012 q = 1) (hb : d149352 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148012, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148012, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d148019 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148024 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d148027 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147928 q = 1) (hb : d149358 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147928, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28254 q ha hb
    | true =>
      simp only [d147928, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28255 q ha hb
  have h13 (q : Pattern) (ha : d148028 q = 1) (hb : d149359 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148028, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d148028, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148031 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148032 q = 1) (hb : d149360 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148032, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148032, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148033 q = 1) (hb : d149361 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148033, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d148033, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148034 q = 1) (hb : d149362 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148034, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d148034, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148035 q = 1) (hb : d149363 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148035, d149363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148035, d149363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro28420 (p : Pattern) (ha : d148060 p = 1) (hb : d149895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148027 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147928 q = 1) (hb : d149358 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147928, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28254 q ha hb
    | true =>
      simp only [d147928, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28255 q ha hb
  have h3 (q : Pattern) (ha : d148028 q = 1) (hb : d149359 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148028, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148028, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148031 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148032 q = 1) (hb : d149360 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148032, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148032, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148058 q = 1) (hb : d149361 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148058, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148058, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148059 q = 1) (hb : d149362 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148059, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148059, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148060 q = 1) (hb : d149895 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148060, d149895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148060, d149895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28421 (p : Pattern) (ha : d148148 p = 1) (hb : d149477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148106 q = 1) (hb : d149462 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148106, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28283 q ha hb
    | true =>
      simp only [d148106, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d148107 q = 1) (hb : d149463 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148107, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148107, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148108 q = 1) (hb : d149464 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148108, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148108, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148114 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148115 q = 1) (hb : d149467 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148115, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28284 q ha hb
    | true =>
      simp only [d148115, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148116 q = 1) (hb : d149468 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148116, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148116, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148117 q = 1) (hb : d149469 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148117, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148117, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148118 q = 1) (hb : d149470 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148118, d149470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148118, d149470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148133 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d148134 q = 1) (hb : d149467 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148134, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28284 q ha hb
    | true =>
      simp only [d148134, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d148135 q = 1) (hb : d149468 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148135, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148135, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148136 q = 1) (hb : d149469 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148136, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148136, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148137 q = 1) (hb : d149475 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148137, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148137, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d148147 q = 1) (hb : d149476 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148147, d149476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148147, d149476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148148 q = 1) (hb : d149477 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148148, d149477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148148, d149477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro28422 (p : Pattern) (ha : d148154 p = 1) (hb : d149491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148149 q = 1) (hb : d149478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148149, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28421 q ha hb
    | true =>
      simp only [d148149, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148150 q = 1) (hb : d149479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148150, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148150, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148140 q = 1) (hb : d149486 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148140, d149486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28288 q ha hb
    | true =>
      simp only [d148140, d149486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148141 q = 1) (hb : d149487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148141, d149487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148141, d149487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148151 q = 1) (hb : d149488 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148151, d149488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148151, d149488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148152 q = 1) (hb : d149489 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148152, d149489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148152, d149489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148153 q = 1) (hb : d149490 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148153, d149490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148153, d149490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148154 q = 1) (hb : d149491 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148154, d149491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148154, d149491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28423 (p : Pattern) (ha : d148179 p = 1) (hb : d149906 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148159 q = 1) (hb : d149901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148159, d149901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28422 q ha hb
    | true =>
      simp only [d148159, d149901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28293 q ha hb
  have h3 (q : Pattern) (ha : d148160 q = 1) (hb : d149902 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148160, d149902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148160, d149902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148175 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148176 q = 1) (hb : d149903 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148176, d149903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148176, d149903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148177 q = 1) (hb : d149904 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148177, d149904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148177, d149904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148178 q = 1) (hb : d149905 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148178, d149905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148178, d149905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148179 q = 1) (hb : d149906 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148179, d149906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148179, d149906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28424 (p : Pattern) (ha : d148192 p = 1) (hb : d149912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148036 q = 1) (hb : d149364 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148036, d149364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28418 q ha hb
    | true =>
      simp only [d148036, d149364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28419 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148054 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148055 q = 1) (hb : d149365 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148055, d149365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148055, d149365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148056 q = 1) (hb : d149893 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148056, d149893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148056, d149893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148057 q = 1) (hb : d149894 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148057, d149894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148057, d149894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148061 q = 1) (hb : d149896 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148061, d149896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148061, d149896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28420 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d148063 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d148064 q = 1) (hb : d149897 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148064, d149897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148064, d149897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d148065 q = 1) (hb : d149898 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148065, d149898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148065, d149898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d148066 q = 1) (hb : d149899 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148066, d149899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148066, d149899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d148067 q = 1) (hb : d149900 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148067, d149900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148067, d149900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148180 q = 1) (hb : d149907 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148180, d149907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148180, d149907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28423 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148187 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148188 q = 1) (hb : d149908 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148188, d149908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148188, d149908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148189 q = 1) (hb : d149909 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148189, d149909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148189, d149909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d148190 q = 1) (hb : d149910 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148190, d149910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d148190, d149910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d148191 q = 1) (hb : d149911 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148191, d149911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148191, d149911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d148192 q = 1) (hb : d149912 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d148192, d149912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148192, d149912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro28425 (p : Pattern) (ha : d148198 p = 1) (hb : d149918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148193 q = 1) (hb : d149913 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d148193, d149913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148193, d149913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28424 q ha hb
  have h2 (q : Pattern) (ha : d148194 q = 1) (hb : d149914 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d148194, d149914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148194, d149914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148195 q = 1) (hb : d149915 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d148195, d149915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148195, d149915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148196 q = 1) (hb : d149916 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d148196, d149916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148196, d149916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148197 q = 1) (hb : d149917 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d148197, d149917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148197, d149917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148198 q = 1) (hb : d149918 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d148198, d149918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148198, d149918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28426 (p : Pattern) (ha : d148332 p = 1) (hb : d149562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148275 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d148312 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d148249 q = 1) (hb : d149557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148249, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28302 q ha hb
    | true =>
      simp only [d148249, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28303 q ha hb
  have h5 (q : Pattern) (ha : d148313 q = 1) (hb : d149558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148313, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d148313, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d148328 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d148329 q = 1) (hb : d149559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148329, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148329, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d148330 q = 1) (hb : d149560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148330, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d148330, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148331 q = 1) (hb : d149561 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148331, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148331, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148332 q = 1) (hb : d149562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148332, d149562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148332, d149562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro28427 (p : Pattern) (ha : d148354 p = 1) (hb : d149572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d148275 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148284 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148312 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148249 q = 1) (hb : d149557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148249, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28302 q ha hb
    | true =>
      simp only [d148249, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28303 q ha hb
  have h4 (q : Pattern) (ha : d148313 q = 1) (hb : d149558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148313, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d148313, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148328 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148329 q = 1) (hb : d149559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148329, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148329, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148330 q = 1) (hb : d149560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148330, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148330, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148331 q = 1) (hb : d149561 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148331, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148331, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d148338 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148343 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d148346 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d148259 q = 1) (hb : d149567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148259, d149567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28305 q ha hb
    | true =>
      simp only [d148259, d149567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28306 q ha hb
  have h13 (q : Pattern) (ha : d148347 q = 1) (hb : d149568 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148347, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d148347, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148350 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148351 q = 1) (hb : d149569 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148351, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148351, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148352 q = 1) (hb : d149570 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148352, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d148352, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148353 q = 1) (hb : d149571 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148353, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d148353, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148354 q = 1) (hb : d149572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148354, d149572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148354, d149572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro28428 (p : Pattern) (ha : d148379 p = 1) (hb : d149925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148346 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148259 q = 1) (hb : d149567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148259, d149567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28305 q ha hb
    | true =>
      simp only [d148259, d149567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28306 q ha hb
  have h3 (q : Pattern) (ha : d148347 q = 1) (hb : d149568 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148347, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148347, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148350 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148351 q = 1) (hb : d149569 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148351, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148351, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148377 q = 1) (hb : d149570 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148377, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148377, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148378 q = 1) (hb : d149571 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148378, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148378, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148379 q = 1) (hb : d149925 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148379, d149925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148379, d149925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28429 (p : Pattern) (ha : d148448 p = 1) (hb : d149686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148405 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148406 q = 1) (hb : d149671 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148406, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28333 q ha hb
    | true =>
      simp only [d148406, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d148407 q = 1) (hb : d149672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148407, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148407, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148408 q = 1) (hb : d149673 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148408, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148408, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148414 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148415 q = 1) (hb : d149676 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148415, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28334 q ha hb
    | true =>
      simp only [d148415, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148416 q = 1) (hb : d149677 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148416, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148416, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148417 q = 1) (hb : d149678 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148417, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148417, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148418 q = 1) (hb : d149679 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148418, d149679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148418, d149679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148433 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d148434 q = 1) (hb : d149676 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148434, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28334 q ha hb
    | true =>
      simp only [d148434, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d148435 q = 1) (hb : d149677 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148435, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148435, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148436 q = 1) (hb : d149678 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148436, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148436, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148437 q = 1) (hb : d149684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148437, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148437, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d148447 q = 1) (hb : d149685 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148447, d149685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148447, d149685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148448 q = 1) (hb : d149686 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148448, d149686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148448, d149686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro28430 (p : Pattern) (ha : d148454 p = 1) (hb : d149700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148449 q = 1) (hb : d149687 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148449, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28429 q ha hb
    | true =>
      simp only [d148449, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148450 q = 1) (hb : d149688 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148450, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148450, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148440 q = 1) (hb : d149695 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148440, d149695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28338 q ha hb
    | true =>
      simp only [d148440, d149695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148441 q = 1) (hb : d149696 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148441, d149696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148441, d149696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148451 q = 1) (hb : d149697 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148451, d149697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148451, d149697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148452 q = 1) (hb : d149698 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148452, d149698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148452, d149698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148453 q = 1) (hb : d149699 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148453, d149699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148453, d149699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148454 q = 1) (hb : d149700 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148454, d149700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148454, d149700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28431 (p : Pattern) (ha : d148479 p = 1) (hb : d149936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148446 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148459 q = 1) (hb : d149931 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148459, d149931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28430 q ha hb
    | true =>
      simp only [d148459, d149931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28343 q ha hb
  have h3 (q : Pattern) (ha : d148460 q = 1) (hb : d149932 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148460, d149932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148460, d149932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148475 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148476 q = 1) (hb : d149933 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148476, d149933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148476, d149933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148477 q = 1) (hb : d149934 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148477, d149934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148477, d149934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148478 q = 1) (hb : d149935 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148478, d149935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148478, d149935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148479 q = 1) (hb : d149936 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148479, d149936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148479, d149936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28432 (p : Pattern) (ha : d148492 p = 1) (hb : d149942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d148267 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148355 q = 1) (hb : d149573 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148355, d149573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28426 q ha hb
    | true =>
      simp only [d148355, d149573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28427 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148373 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148374 q = 1) (hb : d149574 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148374, d149574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148374, d149574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148375 q = 1) (hb : d149923 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148375, d149923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148375, d149923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148376 q = 1) (hb : d149924 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148376, d149924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148376, d149924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148380 q = 1) (hb : d149926 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148380, d149926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148380, d149926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28428 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d148382 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d148383 q = 1) (hb : d149927 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148383, d149927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148383, d149927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d148384 q = 1) (hb : d149928 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148384, d149928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148384, d149928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d148385 q = 1) (hb : d149929 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148385, d149929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148385, d149929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d148386 q = 1) (hb : d149930 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148386, d149930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148386, d149930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148480 q = 1) (hb : d149937 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148480, d149937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148480, d149937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28431 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148487 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148488 q = 1) (hb : d149938 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148488, d149938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148488, d149938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148489 q = 1) (hb : d149939 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148489, d149939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148489, d149939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d148490 q = 1) (hb : d149940 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148490, d149940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d148490, d149940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d148491 q = 1) (hb : d149941 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148491, d149941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148491, d149941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d148492 q = 1) (hb : d149942 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d148492, d149942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148492, d149942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro28433 (p : Pattern) (ha : d148498 p = 1) (hb : d149948 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148493 q = 1) (hb : d149943 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d148493, d149943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148493, d149943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28432 q ha hb
  have h2 (q : Pattern) (ha : d148494 q = 1) (hb : d149944 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d148494, d149944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148494, d149944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148495 q = 1) (hb : d149945 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d148495, d149945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148495, d149945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148496 q = 1) (hb : d149946 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d148496, d149946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148496, d149946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148497 q = 1) (hb : d149947 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d148497, d149947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148497, d149947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148498 q = 1) (hb : d149948 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d148498, d149948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148498, d149948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28434 (p : Pattern) (ha : d148504 p = 1) (hb : d149954 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d147261 q = 1) (hb : d149835 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147261, d149835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28397 q ha hb
    | true =>
      simp only [d147261, d149835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28403 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147500 q = 1) (hb : d149862 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147500, d149862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147500, d149862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28409 q ha hb
  have h3 (q : Pattern) (ha : d147501 q = 1) (hb : d149863 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d147501, d149863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147501, d149863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147858 q = 1) (hb : d149890 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147858, d149890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147858, d149890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28417 q ha hb
  have h5 (q : Pattern) (ha : d147859 q = 1) (hb : d149891 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d147859, d149891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147859, d149891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147860 q = 1) (hb : d149892 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d147860, d149892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147860, d149892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148199 q = 1) (hb : d149919 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d148199, d149919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148199, d149919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28425 q ha hb
  have h8 (q : Pattern) (ha : d148200 q = 1) (hb : d149920 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d148200, d149920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148200, d149920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148201 q = 1) (hb : d149921 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d148201, d149921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148201, d149921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148202 q = 1) (hb : d149922 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d148202, d149922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148202, d149922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148499 q = 1) (hb : d149949 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d148499, d149949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148499, d149949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28433 q ha hb
  have h12 (q : Pattern) (ha : d148500 q = 1) (hb : d149950 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d148500, d149950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148500, d149950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148501 q = 1) (hb : d149951 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d148501, d149951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148501, d149951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148502 q = 1) (hb : d149952 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d148502, d149952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148502, d149952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148503 q = 1) (hb : d149953 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d148503, d149953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148503, d149953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148504 q = 1) (hb : d149954 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d148504, d149954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148504, d149954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro28435 (p : Pattern) (ha : d148510 p = 1) (hb : d149960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148505 q = 1) (hb : d149955 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d148505, d149955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28434 q ha hb
    | true =>
      simp only [d148505, d149955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148506 q = 1) (hb : d149956 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d148506, d149956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148506, d149956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148507 q = 1) (hb : d149957 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d148507, d149957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148507, d149957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148508 q = 1) (hb : d149958 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d148508, d149958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148508, d149958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148509 q = 1) (hb : d149959 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d148509, d149959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148509, d149959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148510 q = 1) (hb : d149960 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d148510, d149960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148510, d149960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28436 (p : Pattern) (ha : d148516 p = 1) (hb : d149966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148511 q = 1) (hb : d149961 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d148511, d149961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28435 q ha hb
    | true =>
      simp only [d148511, d149961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148512 q = 1) (hb : d149962 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d148512, d149962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148512, d149962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148513 q = 1) (hb : d149963 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d148513, d149963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148513, d149963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148514 q = 1) (hb : d149964 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d148514, d149964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148514, d149964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148515 q = 1) (hb : d149965 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d148515, d149965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148515, d149965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148516 q = 1) (hb : d149966 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d148516, d149966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148516, d149966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28437 (p : Pattern) (ha : d148522 p = 1) (hb : d149972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148517 q = 1) (hb : d149967 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d148517, d149967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28436 q ha hb
    | true =>
      simp only [d148517, d149967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148518 q = 1) (hb : d149968 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d148518, d149968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148518, d149968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148519 q = 1) (hb : d149969 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d148519, d149969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148519, d149969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148520 q = 1) (hb : d149970 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d148520, d149970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148520, d149970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148521 q = 1) (hb : d149971 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d148521, d149971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148521, d149971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148522 q = 1) (hb : d149972 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d148522, d149972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148522, d149972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28438 (p : Pattern) (ha : d148528 p = 1) (hb : d149978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148523 q = 1) (hb : d149973 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d148523, d149973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28437 q ha hb
    | true =>
      simp only [d148523, d149973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148524 q = 1) (hb : d149974 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d148524, d149974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148524, d149974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148525 q = 1) (hb : d149975 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d148525, d149975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148525, d149975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148526 q = 1) (hb : d149976 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d148526, d149976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148526, d149976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148527 q = 1) (hb : d149977 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d148527, d149977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148527, d149977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148528 q = 1) (hb : d149978 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d148528, d149978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148528, d149978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28439 (p : Pattern) (ha : d148534 p = 1) (hb : d149984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148529 q = 1) (hb : d149979 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d148529, d149979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28438 q ha hb
    | true =>
      simp only [d148529, d149979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148530 q = 1) (hb : d149980 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d148530, d149980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148530, d149980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148531 q = 1) (hb : d149981 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d148531, d149981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148531, d149981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148532 q = 1) (hb : d149982 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d148532, d149982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148532, d149982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148533 q = 1) (hb : d149983 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d148533, d149983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148533, d149983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148534 q = 1) (hb : d149984 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d148534, d149984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148534, d149984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28440 (p : Pattern) (ha : d148540 p = 1) (hb : d149990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148535 q = 1) (hb : d149985 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d148535, d149985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28439 q ha hb
    | true =>
      simp only [d148535, d149985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148536 q = 1) (hb : d149986 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d148536, d149986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148536, d149986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148537 q = 1) (hb : d149987 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d148537, d149987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148537, d149987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148538 q = 1) (hb : d149988 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d148538, d149988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148538, d149988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148539 q = 1) (hb : d149989 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d148539, d149989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148539, d149989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148540 q = 1) (hb : d149990 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d148540, d149990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148540, d149990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28441 (p : Pattern) (ha : d148546 p = 1) (hb : d149996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148541 q = 1) (hb : d149991 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d148541, d149991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28440 q ha hb
    | true =>
      simp only [d148541, d149991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148542 q = 1) (hb : d149992 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d148542, d149992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148542, d149992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148543 q = 1) (hb : d149993 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d148543, d149993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148543, d149993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148544 q = 1) (hb : d149994 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d148544, d149994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148544, d149994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148545 q = 1) (hb : d149995 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d148545, d149995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148545, d149995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148546 q = 1) (hb : d149996 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d148546, d149996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148546, d149996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28442 (p : Pattern) (ha : d104 p = 1) (hb : d150001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d20906 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d149997 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d149997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d149997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d149998 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d149998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d149998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d149999 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d149999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d149999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d150000 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d150000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d150000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d150001 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d150001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d150001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro28443 (p : Pattern) (ha : d111 p = 1) (hb : d150006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20906 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d100 q = 1) (hb : d149997 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d149997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d149997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d101 q = 1) (hb : d149998 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d149998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101, d149998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102 q = 1) (hb : d149999 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d149999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d149999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d103 q = 1) (hb : d150000 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d150000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d150000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d20913 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d107 q = 1) (hb : d150002 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d150002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107, d150002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108 q = 1) (hb : d150003 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d150003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108, d150003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109 q = 1) (hb : d150004 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d150004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109, d150004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d110 q = 1) (hb : d150005 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d150005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d110, d150005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d111 q = 1) (hb : d150006 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d150006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d111, d150006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro28444 (p : Pattern) (ha : d406 p = 1) (hb : d150013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20913 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d150002 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d150002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d150002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d150003 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d150003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d150003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d150011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d150011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d150011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d150012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d150012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d150012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d150013 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d150013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d150013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28445 (p : Pattern) (ha : d462 p = 1) (hb : d150023 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20945 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d150019 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d150019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d150019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d85 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d150020 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d150020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d150020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d150021 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d150021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d150021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d150022 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d150022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d150022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d150023 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d150023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d150023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28446 (p : Pattern) (ha : d53647 p = 1) (hb : d150029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d150007 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d150007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28442 q ha hb
    | true =>
      simp only [d112, d150007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28443 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d150008 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d150008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d150008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d150009 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d150009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d150009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d150010 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d150010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d150010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d150014 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d150014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d150014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28444 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d150015 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d150015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d150015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d150016 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d150016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d150016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d150017 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d150017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d150017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d150018 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d150018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d150018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d150024 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d150024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d150024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28445 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d150025 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d150025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d150025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d150026 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d150026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d150026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d150027 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d150027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d150027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d150028 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d150028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d150028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d150029 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d150029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d150029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro28447 (p : Pattern) (ha : d148619 p = 1) (hb : d150039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20982 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20988 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21009 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148560 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148615 q = 1) (hb : d150035 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148615, d150035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148615, d150035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21031 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d148616 q = 1) (hb : d150036 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148616, d150036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148616, d150036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148617 q = 1) (hb : d150037 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148617, d150037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148617, d150037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148618 q = 1) (hb : d150038 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148618, d150038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148618, d150038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148619 q = 1) (hb : d150039 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148619, d150039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d148619, d150039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro28448 (p : Pattern) (ha : d148626 p = 1) (hb : d150044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d20982 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20988 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21009 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d148560 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d148615 q = 1) (hb : d150035 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148615, d150035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148615, d150035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21031 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148616 q = 1) (hb : d150036 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148616, d150036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148616, d150036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148617 q = 1) (hb : d150037 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148617, d150037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148617, d150037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148618 q = 1) (hb : d150038 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148618, d150038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d148618, d150038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21040 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21044 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d21046 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d148567 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d148622 q = 1) (hb : d150040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148622, d150040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148622, d150040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21052 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148623 q = 1) (hb : d150041 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148623, d150041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148623, d150041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148624 q = 1) (hb : d150042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148624, d150042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148624, d150042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148625 q = 1) (hb : d150043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148625, d150043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148625, d150043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148626 q = 1) (hb : d150044 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148626, d150044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148626, d150044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro28449 (p : Pattern) (ha : d149786 p = 1) (hb : d150051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21046 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148567 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148622 q = 1) (hb : d150040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148622, d150040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148622, d150040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21052 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148623 q = 1) (hb : d150041 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148623, d150041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148623, d150041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148624 q = 1) (hb : d150049 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148624, d150049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d148624, d150049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148625 q = 1) (hb : d150050 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148625, d150050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d148625, d150050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149786 q = 1) (hb : d150051 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d149786, d150051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149786, d150051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28450 (p : Pattern) (ha : d149796 p = 1) (hb : d150061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21090 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148598 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d149792 q = 1) (hb : d150057 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149792, d150057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149792, d150057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21112 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149793 q = 1) (hb : d150058 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149793, d150058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149793, d150058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149794 q = 1) (hb : d150059 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149794, d150059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149794, d150059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149795 q = 1) (hb : d150060 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d149795, d150060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149795, d150060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149796 q = 1) (hb : d150061 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d149796, d150061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149796, d150061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28451 (p : Pattern) (ha : d149802 p = 1) (hb : d150067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d20976 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148627 q = 1) (hb : d150045 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148627, d150045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28447 q ha hb
    | true =>
      simp only [d148627, d150045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28448 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21059 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148628 q = 1) (hb : d150046 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148628, d150046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148628, d150046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149784 q = 1) (hb : d150047 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d149784, d150047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149784, d150047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149785 q = 1) (hb : d150048 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d149785, d150048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149785, d150048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149787 q = 1) (hb : d150052 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d149787, d150052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149787, d150052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28449 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d149788 q = 1) (hb : d150053 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d149788, d150053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d149788, d150053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d149789 q = 1) (hb : d150054 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d149789, d150054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d149789, d150054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d149790 q = 1) (hb : d150055 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d149790, d150055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d149790, d150055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d149791 q = 1) (hb : d150056 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d149791, d150056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149791, d150056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d149797 q = 1) (hb : d150062 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d149797, d150062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149797, d150062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28450 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d149798 q = 1) (hb : d150063 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d149798, d150063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d149798, d150063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d149799 q = 1) (hb : d150064 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d149799, d150064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d149799, d150064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d149800 q = 1) (hb : d150065 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d149800, d150065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d149800, d150065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d149801 q = 1) (hb : d150066 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d149801, d150066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d149801, d150066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d149802 q = 1) (hb : d150067 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d149802, d150067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d149802, d150067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro28452 (p : Pattern) (ha : d149808 p = 1) (hb : d150073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d150030 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d150030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d150030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28446 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d150031 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d150031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d150031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d150032 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d150032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d150032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d150033 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d150033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d150033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d150034 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d150034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d150034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149803 q = 1) (hb : d150068 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d149803, d150068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149803, d150068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28451 q ha hb
  have h8 (q : Pattern) (ha : d149804 q = 1) (hb : d150069 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d149804, d150069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149804, d150069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d149805 q = 1) (hb : d150070 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d149805, d150070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149805, d150070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d149806 q = 1) (hb : d150071 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d149806, d150071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149806, d150071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d149807 q = 1) (hb : d150072 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d149807, d150072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149807, d150072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d149808 q = 1) (hb : d150073 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d149808, d150073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149808, d150073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro28453 (p : Pattern) (ha : d148759 p = 1) (hb : d150078 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21172 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21181 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21211 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148754 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148755 q = 1) (hb : d150074 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148755, d150074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148755, d150074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21253 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d148756 q = 1) (hb : d150075 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148756, d150075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148756, d150075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148757 q = 1) (hb : d150076 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148757, d150076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148757, d150076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148758 q = 1) (hb : d150077 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148758, d150077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148758, d150077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148759 q = 1) (hb : d150078 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148759, d150078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d148759, d150078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro28454 (p : Pattern) (ha : d148769 p = 1) (hb : d150083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21172 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21181 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21211 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d148754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d148755 q = 1) (hb : d150074 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148755, d150074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148755, d150074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21253 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148756 q = 1) (hb : d150075 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148756, d150075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148756, d150075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148757 q = 1) (hb : d150076 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148757, d150076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148757, d150076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148758 q = 1) (hb : d150077 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148758, d150077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d148758, d150077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21263 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21268 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d21270 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d148764 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d148765 q = 1) (hb : d150079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148765, d150079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148765, d150079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21277 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148766 q = 1) (hb : d150080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148766, d150080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148766, d150080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148767 q = 1) (hb : d150081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148767, d150081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148767, d150081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148768 q = 1) (hb : d150082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148768, d150082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148768, d150082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148769 q = 1) (hb : d150083 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148769, d150083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148769, d150083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro28455 (p : Pattern) (ha : d149811 p = 1) (hb : d150090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21270 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148765 q = 1) (hb : d150079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148765, d150079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148765, d150079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21277 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148766 q = 1) (hb : d150080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148766, d150080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148766, d150080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148767 q = 1) (hb : d150088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148767, d150088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d148767, d150088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148768 q = 1) (hb : d150089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148768, d150089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d148768, d150089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149811 q = 1) (hb : d150090 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d149811, d150090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149811, d150090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28456 (p : Pattern) (ha : d149822 p = 1) (hb : d150100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21349 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d149817 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d149818 q = 1) (hb : d150096 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149818, d150096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149818, d150096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21389 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149819 q = 1) (hb : d150097 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149819, d150097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149819, d150097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149820 q = 1) (hb : d150098 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149820, d150098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149820, d150098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149821 q = 1) (hb : d150099 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d149821, d150099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149821, d150099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149822 q = 1) (hb : d150100 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d149822, d150100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149822, d150100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28457 (p : Pattern) (ha : d149828 p = 1) (hb : d150106 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21164 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148770 q = 1) (hb : d150084 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148770, d150084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28453 q ha hb
    | true =>
      simp only [d148770, d150084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28454 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21295 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148771 q = 1) (hb : d150085 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148771, d150085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148771, d150085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149809 q = 1) (hb : d150086 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d149809, d150086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149809, d150086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149810 q = 1) (hb : d150087 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d149810, d150087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149810, d150087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149812 q = 1) (hb : d150091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d149812, d150091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149812, d150091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28455 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d21304 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d149813 q = 1) (hb : d150092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d149813, d150092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d149813, d150092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d149814 q = 1) (hb : d150093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d149814, d150093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d149814, d150093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d149815 q = 1) (hb : d150094 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d149815, d150094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d149815, d150094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d149816 q = 1) (hb : d150095 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d149816, d150095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149816, d150095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d149823 q = 1) (hb : d150101 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d149823, d150101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149823, d150101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28456 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21405 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d149824 q = 1) (hb : d150102 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d149824, d150102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d149824, d150102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d149825 q = 1) (hb : d150103 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d149825, d150103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d149825, d150103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d149826 q = 1) (hb : d150104 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d149826, d150104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d149826, d150104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d149827 q = 1) (hb : d150105 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d149827, d150105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d149827, d150105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d149828 q = 1) (hb : d150106 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d149828, d150106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d149828, d150106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro28458 (p : Pattern) (ha : d149834 p = 1) (hb : d150112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d149829 q = 1) (hb : d150107 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d149829, d150107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149829, d150107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28457 q ha hb
  have h2 (q : Pattern) (ha : d149830 q = 1) (hb : d150108 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d149830, d150108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149830, d150108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d149831 q = 1) (hb : d150109 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d149831, d150109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149831, d150109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d149832 q = 1) (hb : d150110 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d149832, d150110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149832, d150110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d149833 q = 1) (hb : d150111 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d149833, d150111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149833, d150111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149834 q = 1) (hb : d150112 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d149834, d150112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149834, d150112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28459 (p : Pattern) (ha : d148947 p = 1) (hb : d150118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21471 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21480 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21510 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148942 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148943 q = 1) (hb : d150114 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148943, d150114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148943, d150114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21556 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d148944 q = 1) (hb : d150115 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148944, d150115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148944, d150115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148945 q = 1) (hb : d150116 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148945, d150116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148945, d150116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148946 q = 1) (hb : d150117 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148946, d150117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148946, d150117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148947 q = 1) (hb : d150118 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148947, d150118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d148947, d150118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro28460 (p : Pattern) (ha : d148957 p = 1) (hb : d150123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21480 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21510 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d148942 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d148943 q = 1) (hb : d150114 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148943, d150114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148943, d150114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21556 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148944 q = 1) (hb : d150115 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148944, d150115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148944, d150115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148945 q = 1) (hb : d150116 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148945, d150116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148945, d150116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148946 q = 1) (hb : d150117 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148946, d150117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d148946, d150117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21566 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21571 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d21573 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d148952 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d148953 q = 1) (hb : d150119 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148953, d150119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148953, d150119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21580 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148954 q = 1) (hb : d150120 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148954, d150120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148954, d150120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148955 q = 1) (hb : d150121 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148955, d150121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148955, d150121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148956 q = 1) (hb : d150122 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148956, d150122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148956, d150122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148957 q = 1) (hb : d150123 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148957, d150123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148957, d150123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro28461 (p : Pattern) (ha : d149838 p = 1) (hb : d150130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21573 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148952 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148953 q = 1) (hb : d150119 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148953, d150119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148953, d150119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21580 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148954 q = 1) (hb : d150120 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148954, d150120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148954, d150120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148955 q = 1) (hb : d150128 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148955, d150128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d148955, d150128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148956 q = 1) (hb : d150129 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148956, d150129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d148956, d150129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149838 q = 1) (hb : d150130 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d149838, d150130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149838, d150130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28462 (p : Pattern) (ha : d149849 p = 1) (hb : d150140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d149844 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d149845 q = 1) (hb : d150136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149845, d150136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149845, d150136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21706 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149846 q = 1) (hb : d150137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149846, d150137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149846, d150137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149847 q = 1) (hb : d150138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149847, d150138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149847, d150138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149848 q = 1) (hb : d150139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d149848, d150139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149848, d150139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149849 q = 1) (hb : d150140 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d149849, d150140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149849, d150140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28463 (p : Pattern) (ha : d149855 p = 1) (hb : d150146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21463 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148958 q = 1) (hb : d150124 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148958, d150124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28459 q ha hb
    | true =>
      simp only [d148958, d150124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28460 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21598 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148959 q = 1) (hb : d150125 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148959, d150125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148959, d150125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149836 q = 1) (hb : d150126 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d149836, d150126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149836, d150126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149837 q = 1) (hb : d150127 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d149837, d150127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149837, d150127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149839 q = 1) (hb : d150131 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d149839, d150131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149839, d150131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28461 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d21607 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d149840 q = 1) (hb : d150132 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d149840, d150132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d149840, d150132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d149841 q = 1) (hb : d150133 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d149841, d150133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d149841, d150133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d149842 q = 1) (hb : d150134 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d149842, d150134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d149842, d150134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d149843 q = 1) (hb : d150135 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d149843, d150135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149843, d150135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d149850 q = 1) (hb : d150141 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d149850, d150141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149850, d150141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28462 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21722 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d149851 q = 1) (hb : d150142 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d149851, d150142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d149851, d150142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d149852 q = 1) (hb : d150143 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d149852, d150143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d149852, d150143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d149853 q = 1) (hb : d150144 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d149853, d150144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d149853, d150144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d149854 q = 1) (hb : d150145 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d149854, d150145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d149854, d150145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d149855 q = 1) (hb : d150146 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d149855, d150146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d149855, d150146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro28464 (p : Pattern) (ha : d149861 p = 1) (hb : d150152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d149856 q = 1) (hb : d150147 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d149856, d150147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149856, d150147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28463 q ha hb
  have h2 (q : Pattern) (ha : d149857 q = 1) (hb : d150148 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d149857, d150148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149857, d150148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d149858 q = 1) (hb : d150149 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d149858, d150149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149858, d150149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d149859 q = 1) (hb : d150150 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d149859, d150150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149859, d150150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d149860 q = 1) (hb : d150151 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d149860, d150151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149860, d150151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149861 q = 1) (hb : d150152 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d149861, d150152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149861, d150152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28465 (p : Pattern) (ha : d149145 p = 1) (hb : d150159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21824 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21833 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21878 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d149140 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149141 q = 1) (hb : d150155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149141, d150155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149141, d150155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21962 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d149142 q = 1) (hb : d150156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149142, d150156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149142, d150156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149143 q = 1) (hb : d150157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149143, d150157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d149143, d150157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d149144 q = 1) (hb : d150158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d149144, d150158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149144, d150158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d149145 q = 1) (hb : d150159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d149145, d150159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149145, d150159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro28466 (p : Pattern) (ha : d149155 p = 1) (hb : d150164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21824 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21833 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21878 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d149140 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d149141 q = 1) (hb : d150155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149141, d150155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d149141, d150155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21962 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d149142 q = 1) (hb : d150156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149142, d150156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149142, d150156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149143 q = 1) (hb : d150157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149143, d150157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149143, d150157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149144 q = 1) (hb : d150158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d149144, d150158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149144, d150158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21972 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21977 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d21980 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d149150 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d149151 q = 1) (hb : d150160 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149151, d150160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d149151, d150160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21987 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d149152 q = 1) (hb : d150161 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149152, d150161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d149152, d150161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d149153 q = 1) (hb : d150162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149153, d150162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d149153, d150162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d149154 q = 1) (hb : d150163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d149154, d150163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d149154, d150163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d149155 q = 1) (hb : d150164 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d149155, d150164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d149155, d150164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro28467 (p : Pattern) (ha : d149866 p = 1) (hb : d150171 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d149150 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d149151 q = 1) (hb : d150160 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149151, d150160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149151, d150160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21987 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149152 q = 1) (hb : d150161 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149152, d150161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149152, d150161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149153 q = 1) (hb : d150169 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149153, d150169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149153, d150169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149154 q = 1) (hb : d150170 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d149154, d150170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149154, d150170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149866 q = 1) (hb : d150171 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d149866, d150171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149866, d150171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28468 (p : Pattern) (ha : d149877 p = 1) (hb : d150181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22110 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d149872 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d149873 q = 1) (hb : d150177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149873, d150177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149873, d150177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22188 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149874 q = 1) (hb : d150178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149874, d150178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149874, d150178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149875 q = 1) (hb : d150179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149875, d150179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149875, d150179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149876 q = 1) (hb : d150180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d149876, d150180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149876, d150180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149877 q = 1) (hb : d150181 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d149877, d150181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149877, d150181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28469 (p : Pattern) (ha : d149883 p = 1) (hb : d150187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21816 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d149156 q = 1) (hb : d150165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d149156, d150165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28465 q ha hb
    | true =>
      simp only [d149156, d150165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28466 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22010 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d149157 q = 1) (hb : d150166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d149157, d150166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149157, d150166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149864 q = 1) (hb : d150167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d149864, d150167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149864, d150167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149865 q = 1) (hb : d150168 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d149865, d150168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149865, d150168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149867 q = 1) (hb : d150172 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d149867, d150172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149867, d150172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28467 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d22019 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d149868 q = 1) (hb : d150173 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d149868, d150173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d149868, d150173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d149869 q = 1) (hb : d150174 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d149869, d150174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d149869, d150174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d149870 q = 1) (hb : d150175 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d149870, d150175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d149870, d150175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d149871 q = 1) (hb : d150176 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d149871, d150176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149871, d150176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d149878 q = 1) (hb : d150182 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d149878, d150182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149878, d150182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28468 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22204 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d149879 q = 1) (hb : d150183 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d149879, d150183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d149879, d150183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d149880 q = 1) (hb : d150184 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d149880, d150184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d149880, d150184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d149881 q = 1) (hb : d150185 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d149881, d150185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d149881, d150185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d149882 q = 1) (hb : d150186 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d149882, d150186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d149882, d150186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d149883 q = 1) (hb : d150187 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d149883, d150187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d149883, d150187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro28470 (p : Pattern) (ha : d149889 p = 1) (hb : d150193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d149884 q = 1) (hb : d150188 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d149884, d150188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149884, d150188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28469 q ha hb
  have h2 (q : Pattern) (ha : d149885 q = 1) (hb : d150189 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d149885, d150189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149885, d150189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d149886 q = 1) (hb : d150190 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d149886, d150190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149886, d150190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d149887 q = 1) (hb : d150191 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d149887, d150191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149887, d150191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d149888 q = 1) (hb : d150192 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d149888, d150192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149888, d150192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149889 q = 1) (hb : d150193 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d149889, d150193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149889, d150193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28471 (p : Pattern) (ha : d149353 p = 1) (hb : d150201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22302 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d22351 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d149348 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149349 q = 1) (hb : d150197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149349, d150197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149349, d150197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d22435 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d149350 q = 1) (hb : d150198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149350, d150198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149350, d150198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149351 q = 1) (hb : d150199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149351, d150199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d149351, d150199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d149352 q = 1) (hb : d150200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d149352, d150200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149352, d150200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d149353 q = 1) (hb : d150201 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d149353, d150201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149353, d150201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro28472 (p : Pattern) (ha : d149363 p = 1) (hb : d150206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22302 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22311 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d149348 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d149349 q = 1) (hb : d150197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149349, d150197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d149349, d150197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22435 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d149350 q = 1) (hb : d150198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149350, d150198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149350, d150198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149351 q = 1) (hb : d150199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149351, d150199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149351, d150199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149352 q = 1) (hb : d150200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d149352, d150200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149352, d150200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d22445 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22450 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d22453 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d149358 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d149359 q = 1) (hb : d150202 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149359, d150202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d149359, d150202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22460 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d149360 q = 1) (hb : d150203 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149360, d150203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d149360, d150203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d149361 q = 1) (hb : d150204 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149361, d150204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d149361, d150204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d149362 q = 1) (hb : d150205 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d149362, d150205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d149362, d150205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d149363 q = 1) (hb : d150206 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d149363, d150206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d149363, d150206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro28473 (p : Pattern) (ha : d149895 p = 1) (hb : d150213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22453 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d149358 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d149359 q = 1) (hb : d150202 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149359, d150202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149359, d150202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22460 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149360 q = 1) (hb : d150203 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149360, d150203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149360, d150203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149361 q = 1) (hb : d150211 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149361, d150211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149361, d150211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149362 q = 1) (hb : d150212 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d149362, d150212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149362, d150212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149895 q = 1) (hb : d150213 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d149895, d150213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149895, d150213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28474 (p : Pattern) (ha : d149906 p = 1) (hb : d150223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22575 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d149901 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d149902 q = 1) (hb : d150219 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149902, d150219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149902, d150219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22653 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149903 q = 1) (hb : d150220 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149903, d150220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149903, d150220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149904 q = 1) (hb : d150221 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149904, d150221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149904, d150221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149905 q = 1) (hb : d150222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d149905, d150222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149905, d150222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149906 q = 1) (hb : d150223 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d149906, d150223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149906, d150223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28475 (p : Pattern) (ha : d149912 p = 1) (hb : d150229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d149364 q = 1) (hb : d150207 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d149364, d150207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28471 q ha hb
    | true =>
      simp only [d149364, d150207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28472 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22483 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d149365 q = 1) (hb : d150208 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d149365, d150208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149365, d150208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149893 q = 1) (hb : d150209 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d149893, d150209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149893, d150209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149894 q = 1) (hb : d150210 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d149894, d150210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149894, d150210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149896 q = 1) (hb : d150214 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d149896, d150214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149896, d150214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28473 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d22492 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d149897 q = 1) (hb : d150215 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d149897, d150215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d149897, d150215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d149898 q = 1) (hb : d150216 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d149898, d150216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d149898, d150216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d149899 q = 1) (hb : d150217 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d149899, d150217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d149899, d150217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d149900 q = 1) (hb : d150218 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d149900, d150218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149900, d150218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d149907 q = 1) (hb : d150224 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d149907, d150224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149907, d150224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28474 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22669 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d149908 q = 1) (hb : d150225 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d149908, d150225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d149908, d150225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d149909 q = 1) (hb : d150226 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d149909, d150226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d149909, d150226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d149910 q = 1) (hb : d150227 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d149910, d150227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d149910, d150227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d149911 q = 1) (hb : d150228 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d149911, d150228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d149911, d150228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d149912 q = 1) (hb : d150229 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d149912, d150229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d149912, d150229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro28476 (p : Pattern) (ha : d149918 p = 1) (hb : d150235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d149913 q = 1) (hb : d150230 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d149913, d150230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149913, d150230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28475 q ha hb
  have h2 (q : Pattern) (ha : d149914 q = 1) (hb : d150231 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d149914, d150231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149914, d150231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d149915 q = 1) (hb : d150232 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d149915, d150232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149915, d150232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d149916 q = 1) (hb : d150233 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d149916, d150233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149916, d150233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d149917 q = 1) (hb : d150234 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d149917, d150234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149917, d150234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149918 q = 1) (hb : d150235 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d149918, d150235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149918, d150235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28477 (p : Pattern) (ha : d149562 p = 1) (hb : d150244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22757 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22766 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d22794 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d149557 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149558 q = 1) (hb : d150240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149558, d150240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149558, d150240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d22868 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d149559 q = 1) (hb : d150241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149559, d150241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149559, d150241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149560 q = 1) (hb : d150242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149560, d150242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d149560, d150242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d149561 q = 1) (hb : d150243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d149561, d150243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149561, d150243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d149562 q = 1) (hb : d150244 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d149562, d150244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149562, d150244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro28478 (p : Pattern) (ha : d149572 p = 1) (hb : d150249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22757 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22794 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d149557 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d149558 q = 1) (hb : d150240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149558, d150240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d149558, d150240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22868 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d149559 q = 1) (hb : d150241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149559, d150241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149559, d150241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149560 q = 1) (hb : d150242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149560, d150242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149560, d150242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149561 q = 1) (hb : d150243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d149561, d150243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149561, d150243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d22878 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22883 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d22886 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d149567 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d149568 q = 1) (hb : d150245 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149568, d150245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d149568, d150245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22893 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d149569 q = 1) (hb : d150246 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149569, d150246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d149569, d150246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d149570 q = 1) (hb : d150247 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149570, d150247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d149570, d150247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d149571 q = 1) (hb : d150248 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d149571, d150248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d149571, d150248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d149572 q = 1) (hb : d150249 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d149572, d150249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d149572, d150249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro28479 (p : Pattern) (ha : d149925 p = 1) (hb : d150256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22886 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d149567 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d149568 q = 1) (hb : d150245 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149568, d150245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149568, d150245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22893 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149569 q = 1) (hb : d150246 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149569, d150246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149569, d150246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149570 q = 1) (hb : d150254 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149570, d150254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149570, d150254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149571 q = 1) (hb : d150255 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d149571, d150255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149571, d150255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149925 q = 1) (hb : d150256 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d149925, d150256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149925, d150256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28480 (p : Pattern) (ha : d149936 p = 1) (hb : d150266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d149931 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d149932 q = 1) (hb : d150262 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149932, d150262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149932, d150262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23059 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149933 q = 1) (hb : d150263 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149933, d150263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149933, d150263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149934 q = 1) (hb : d150264 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149934, d150264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149934, d150264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149935 q = 1) (hb : d150265 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d149935, d150265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149935, d150265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149936 q = 1) (hb : d150266 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d149936, d150266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149936, d150266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28481 (p : Pattern) (ha : d149942 p = 1) (hb : d150272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d149573 q = 1) (hb : d150250 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d149573, d150250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28477 q ha hb
    | true =>
      simp only [d149573, d150250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28478 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22916 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d149574 q = 1) (hb : d150251 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d149574, d150251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149574, d150251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149923 q = 1) (hb : d150252 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d149923, d150252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149923, d150252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149924 q = 1) (hb : d150253 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d149924, d150253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149924, d150253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149926 q = 1) (hb : d150257 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d149926, d150257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149926, d150257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28479 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d22925 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d149927 q = 1) (hb : d150258 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d149927, d150258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d149927, d150258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d149928 q = 1) (hb : d150259 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d149928, d150259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d149928, d150259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d149929 q = 1) (hb : d150260 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d149929, d150260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d149929, d150260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d149930 q = 1) (hb : d150261 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d149930, d150261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149930, d150261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d149937 q = 1) (hb : d150267 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d149937, d150267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149937, d150267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28480 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23075 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d149938 q = 1) (hb : d150268 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d149938, d150268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d149938, d150268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d149939 q = 1) (hb : d150269 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d149939, d150269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d149939, d150269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d149940 q = 1) (hb : d150270 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d149940, d150270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d149940, d150270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d149941 q = 1) (hb : d150271 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d149941, d150271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d149941, d150271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d149942 q = 1) (hb : d150272 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d149942, d150272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d149942, d150272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro28482 (p : Pattern) (ha : d149948 p = 1) (hb : d150278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d149943 q = 1) (hb : d150273 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d149943, d150273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149943, d150273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28481 q ha hb
  have h2 (q : Pattern) (ha : d149944 q = 1) (hb : d150274 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d149944, d150274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149944, d150274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d149945 q = 1) (hb : d150275 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d149945, d150275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149945, d150275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d149946 q = 1) (hb : d150276 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d149946, d150276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149946, d150276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d149947 q = 1) (hb : d150277 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d149947, d150277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149947, d150277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149948 q = 1) (hb : d150278 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d149948, d150278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149948, d150278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28483 (p : Pattern) (ha : d149954 p = 1) (hb : d150284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d149835 q = 1) (hb : d150113 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d149835, d150113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28452 q ha hb
    | true =>
      simp only [d149835, d150113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28458 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d149862 q = 1) (hb : d150153 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d149862, d150153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149862, d150153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28464 q ha hb
  have h3 (q : Pattern) (ha : d149863 q = 1) (hb : d150154 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d149863, d150154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d149863, d150154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d149890 q = 1) (hb : d150194 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d149890, d150194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149890, d150194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28470 q ha hb
  have h5 (q : Pattern) (ha : d149891 q = 1) (hb : d150195 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d149891, d150195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149891, d150195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d149892 q = 1) (hb : d150196 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d149892, d150196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149892, d150196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d149919 q = 1) (hb : d150236 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d149919, d150236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149919, d150236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28476 q ha hb
  have h8 (q : Pattern) (ha : d149920 q = 1) (hb : d150237 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d149920, d150237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149920, d150237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d149921 q = 1) (hb : d150238 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d149921, d150238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149921, d150238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d149922 q = 1) (hb : d150239 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d149922, d150239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149922, d150239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d149949 q = 1) (hb : d150279 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d149949, d150279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149949, d150279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28482 q ha hb
  have h12 (q : Pattern) (ha : d149950 q = 1) (hb : d150280 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d149950, d150280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149950, d150280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d149951 q = 1) (hb : d150281 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d149951, d150281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149951, d150281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d149952 q = 1) (hb : d150282 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d149952, d150282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149952, d150282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d149953 q = 1) (hb : d150283 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d149953, d150283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d149953, d150283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d149954 q = 1) (hb : d150284 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d149954, d150284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d149954, d150284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro28484 (p : Pattern) (ha : d149960 p = 1) (hb : d150290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d149955 q = 1) (hb : d150285 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d149955, d150285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28483 q ha hb
    | true =>
      simp only [d149955, d150285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d149956 q = 1) (hb : d150286 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d149956, d150286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149956, d150286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d149957 q = 1) (hb : d150287 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d149957, d150287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d149957, d150287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d149958 q = 1) (hb : d150288 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d149958, d150288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149958, d150288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d149959 q = 1) (hb : d150289 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d149959, d150289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149959, d150289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d149960 q = 1) (hb : d150290 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d149960, d150290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149960, d150290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28485 (p : Pattern) (ha : d149966 p = 1) (hb : d150296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d149961 q = 1) (hb : d150291 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d149961, d150291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28484 q ha hb
    | true =>
      simp only [d149961, d150291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d149962 q = 1) (hb : d150292 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d149962, d150292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149962, d150292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d149963 q = 1) (hb : d150293 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d149963, d150293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d149963, d150293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d149964 q = 1) (hb : d150294 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d149964, d150294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149964, d150294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d149965 q = 1) (hb : d150295 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d149965, d150295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149965, d150295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d149966 q = 1) (hb : d150296 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d149966, d150296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149966, d150296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28486 (p : Pattern) (ha : d149972 p = 1) (hb : d150302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d149967 q = 1) (hb : d150297 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d149967, d150297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28485 q ha hb
    | true =>
      simp only [d149967, d150297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d149968 q = 1) (hb : d150298 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d149968, d150298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149968, d150298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d149969 q = 1) (hb : d150299 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d149969, d150299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d149969, d150299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d149970 q = 1) (hb : d150300 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d149970, d150300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149970, d150300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d149971 q = 1) (hb : d150301 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d149971, d150301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149971, d150301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d149972 q = 1) (hb : d150302 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d149972, d150302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149972, d150302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28487 (p : Pattern) (ha : d149978 p = 1) (hb : d150308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d149973 q = 1) (hb : d150303 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d149973, d150303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28486 q ha hb
    | true =>
      simp only [d149973, d150303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d149974 q = 1) (hb : d150304 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d149974, d150304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149974, d150304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d149975 q = 1) (hb : d150305 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d149975, d150305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d149975, d150305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d149976 q = 1) (hb : d150306 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d149976, d150306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149976, d150306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d149977 q = 1) (hb : d150307 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d149977, d150307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149977, d150307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d149978 q = 1) (hb : d150308 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d149978, d150308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149978, d150308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28488 (p : Pattern) (ha : d149984 p = 1) (hb : d150314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d149979 q = 1) (hb : d150309 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d149979, d150309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28487 q ha hb
    | true =>
      simp only [d149979, d150309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d149980 q = 1) (hb : d150310 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d149980, d150310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149980, d150310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d149981 q = 1) (hb : d150311 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d149981, d150311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d149981, d150311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d149982 q = 1) (hb : d150312 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d149982, d150312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149982, d150312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d149983 q = 1) (hb : d150313 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d149983, d150313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149983, d150313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d149984 q = 1) (hb : d150314 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d149984, d150314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149984, d150314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28489 (p : Pattern) (ha : d149990 p = 1) (hb : d150320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d149985 q = 1) (hb : d150315 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d149985, d150315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28488 q ha hb
    | true =>
      simp only [d149985, d150315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d149986 q = 1) (hb : d150316 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d149986, d150316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149986, d150316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d149987 q = 1) (hb : d150317 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d149987, d150317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d149987, d150317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d149988 q = 1) (hb : d150318 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d149988, d150318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149988, d150318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d149989 q = 1) (hb : d150319 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d149989, d150319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149989, d150319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d149990 q = 1) (hb : d150320 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d149990, d150320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149990, d150320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28490 (p : Pattern) (ha : d149996 p = 1) (hb : d150326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d149991 q = 1) (hb : d150321 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d149991, d150321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28489 q ha hb
    | true =>
      simp only [d149991, d150321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d149992 q = 1) (hb : d150322 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d149992, d150322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149992, d150322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d149993 q = 1) (hb : d150323 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d149993, d150323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d149993, d150323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d149994 q = 1) (hb : d150324 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d149994, d150324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149994, d150324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d149995 q = 1) (hb : d150325 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d149995, d150325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149995, d150325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d149996 q = 1) (hb : d150326 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d149996, d150326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149996, d150326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28491 (p : Pattern) (ha : d12227 p = 1) (hb : d115574 p = 1) : d115576 p = 1 := by
  have h0 (q : Pattern) (ha : d4821 q = 1) (hb : d94753 q = 1) : d4821 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12225 q = 1) (hb : d115574 q = 1) : d4822 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12225, d115574, d4822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12225, d115574, d4822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d34 q = 1) (hb : d115574 q = 1) : d34 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12226 q = 1) (hb : d115574 q = 1) : d115575 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12226, d115575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12226, d115575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12227 q = 1) (hb : d115574 q = 1) : d115576 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12227, d115576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12227, d115576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28492 (p : Pattern) (ha : d12233 p = 1) (hb : d115574 p = 1) : d115582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28491 q ha hb
    | true =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d115574 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d115574 q = 1) : d115579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12231 q = 1) (hb : d115574 q = 1) : d115580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12231, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12232 q = 1) (hb : d115574 q = 1) : d115581 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12232, d115581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12232, d115581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12233 q = 1) (hb : d115574 q = 1) : d115582 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12233, d115582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12233, d115582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28493 (p : Pattern) (ha : d115242 p = 1) (hb : d115574 p = 1) : d115588 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d115574 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d115574 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d115574 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12234 q = 1) (hb : d115574 q = 1) : d115583 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28492 q ha hb
    | true =>
      simp only [d12234, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115238 q = 1) (hb : d115574 q = 1) : d115584 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115238, d115584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115238, d115584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d115574 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115239 q = 1) (hb : d115574 q = 1) : d115585 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115239, d115585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115239, d115585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115240 q = 1) (hb : d115574 q = 1) : d115586 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115240, d115586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115240, d115586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115241 q = 1) (hb : d115574 q = 1) : d115587 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115241, d115587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115241, d115587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115242 q = 1) (hb : d115574 q = 1) : d115588 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115242, d115588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115242, d115588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro28494 (p : Pattern) (ha : d12240 p = 1) (hb : d115574 p = 1) : d115589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28491 q ha hb
    | true =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d115574 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d115574 q = 1) : d115579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12231 q = 1) (hb : d115574 q = 1) : d115580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12231, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12232 q = 1) (hb : d115574 q = 1) : d115581 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12232, d115581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12232, d115581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12240 q = 1) (hb : d115574 q = 1) : d115589 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12240, d115589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12240, d115589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28495 (p : Pattern) (ha : d115247 p = 1) (hb : d115574 p = 1) : d115595 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d115574 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d115574 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d115574 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12234 q = 1) (hb : d115574 q = 1) : d115583 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28492 q ha hb
    | true =>
      simp only [d12234, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115238 q = 1) (hb : d115574 q = 1) : d115584 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115238, d115584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115238, d115584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d115574 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115239 q = 1) (hb : d115574 q = 1) : d115585 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115239, d115585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115239, d115585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115240 q = 1) (hb : d115574 q = 1) : d115586 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115240, d115586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115240, d115586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115241 q = 1) (hb : d115574 q = 1) : d115587 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115241, d115587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115241, d115587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d115574 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d115574 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d115574 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d12241 q = 1) (hb : d115574 q = 1) : d115590 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d115590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28494 q ha hb
    | true =>
      simp only [d12241, d115590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115243 q = 1) (hb : d115574 q = 1) : d115591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115243, d115591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115243, d115591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d115574 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d115244 q = 1) (hb : d115574 q = 1) : d115592 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115244, d115592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115244, d115592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115245 q = 1) (hb : d115574 q = 1) : d115593 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115245, d115593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115245, d115593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115246 q = 1) (hb : d115574 q = 1) : d115594 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115246, d115594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115246, d115594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d115247 q = 1) (hb : d115574 q = 1) : d115595 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115247, d115595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115247, d115595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro28496 (p : Pattern) (ha : d115254 p = 1) (hb : d115574 p = 1) : d115602 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d115574 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12241 q = 1) (hb : d115574 q = 1) : d115590 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d115590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28494 q ha hb
    | true =>
      simp only [d12241, d115590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115243 q = 1) (hb : d115574 q = 1) : d115591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115243, d115591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115243, d115591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d115574 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115244 q = 1) (hb : d115574 q = 1) : d115592 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115244, d115592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115244, d115592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115252 q = 1) (hb : d115574 q = 1) : d115600 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115252, d115600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115252, d115600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115253 q = 1) (hb : d115574 q = 1) : d115601 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115253, d115601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115253, d115601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115254 q = 1) (hb : d115574 q = 1) : d115602 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115254, d115602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115254, d115602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28497 (p : Pattern) (ha : d12261 p = 1) (hb : d115574 p = 1) : d115609 p = 1 := by
  have h0 (q : Pattern) (ha : d6081 q = 1) (hb : d94753 q = 1) : d6081 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12259 q = 1) (hb : d115574 q = 1) : d6082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12259, d115574, d6082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12259, d115574, d6082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d75 q = 1) (hb : d115574 q = 1) : d75 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12260 q = 1) (hb : d115574 q = 1) : d115608 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12260, d115608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12260, d115608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12261 q = 1) (hb : d115574 q = 1) : d115609 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12261, d115609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12261, d115609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28498 (p : Pattern) (ha : d12267 p = 1) (hb : d115574 p = 1) : d115615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12262 q = 1) (hb : d115574 q = 1) : d115610 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d115610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28497 q ha hb
    | true =>
      simp only [d12262, d115610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12263 q = 1) (hb : d115574 q = 1) : d115611 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d115611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d115611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d115574 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12264 q = 1) (hb : d115574 q = 1) : d115612 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12264, d115612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12264, d115612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12265 q = 1) (hb : d115574 q = 1) : d115613 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12265, d115613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12265, d115613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12266 q = 1) (hb : d115574 q = 1) : d115614 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12266, d115614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12266, d115614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12267 q = 1) (hb : d115574 q = 1) : d115615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12267, d115615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12267, d115615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28499 (p : Pattern) (ha : d115264 p = 1) (hb : d115574 p = 1) : d115621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d115574 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12268 q = 1) (hb : d115574 q = 1) : d115616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12268, d115616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28498 q ha hb
    | true =>
      simp only [d12268, d115616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115260 q = 1) (hb : d115574 q = 1) : d115617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115260, d115617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115260, d115617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d115574 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115261 q = 1) (hb : d115574 q = 1) : d115618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115261, d115618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115261, d115618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115262 q = 1) (hb : d115574 q = 1) : d115619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115262, d115619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115262, d115619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115263 q = 1) (hb : d115574 q = 1) : d115620 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115263, d115620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115263, d115620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115264 q = 1) (hb : d115574 q = 1) : d115621 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115264, d115621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115264, d115621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
