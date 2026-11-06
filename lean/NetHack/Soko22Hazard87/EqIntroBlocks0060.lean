import NetHack.Soko22Hazard87.EqIntroBlocks0059
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro15000 (p : Pattern) (selected : d164915 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (selected : d164914 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10521 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6879 q selected
    | true =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10523 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164915 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15001 (p : Pattern) (selected : d164921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164904 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14997 q selected
    | true =>
      simp only [d164904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14998 q selected
  have h2 (q : Pattern) (selected : d164905 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164906 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164910 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14998 q selected
    | true =>
      simp only [d164910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14999 q selected
  have h5 (q : Pattern) (selected : d164911 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164912 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164913 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164916 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14998 q selected
    | true =>
      simp only [d164916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15000 q selected
  have h9 (q : Pattern) (selected : d164917 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164918 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164919 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164920 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164921 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d164921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro15002 (p : Pattern) (selected : d164925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164916 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14998 q selected
    | true =>
      simp only [d164916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15000 q selected
  have h2 (q : Pattern) (selected : d164917 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164918 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164919 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164924 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164925 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15003 (p : Pattern) (selected : d164931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164922 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15001 q selected
    | true =>
      simp only [d164922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164923 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164926 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15002 q selected
    | true =>
      simp only [d164926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164927 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164928 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164929 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164930 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164931 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15004 (p : Pattern) (selected : d164935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164926 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15002 q selected
    | true =>
      simp only [d164926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164927 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164932 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164933 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164934 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164935 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15005 (p : Pattern) (selected : d164956 p = 1) : d166395 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164859 q = 1) : d164859 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d164868 q = 1) : d164868 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d164897 q = 1) : d164897 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d164936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15003 q selected
    | true =>
      simp only [d164936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15004 q selected
  have h5 (q : Pattern) (selected : d164937 q = 1) : d166391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164937, d166391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164937, d166391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164952 q = 1) : d164952 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d164953 q = 1) : d166392 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164953, d166392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164953, d166392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164954 q = 1) : d166393 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164954, d166393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164954, d166393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164955 q = 1) : d166394 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164955, d166394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164955, d166394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164956 q = 1) : d166395 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164956, d166395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164956, d166395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro15006 (p : Pattern) (selected : d164971 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164922 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15001 q selected
    | true =>
      simp only [d164922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164923 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164926 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15002 q selected
    | true =>
      simp only [d164926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164927 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164928 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164929 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164930 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164971 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15007 (p : Pattern) (selected : d164972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164926 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15002 q selected
    | true =>
      simp only [d164926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164927 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164932 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164933 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164934 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164972 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15008 (p : Pattern) (selected : d164981 p = 1) : d166400 p = 1 := by
  have h0 (q : Pattern) (selected : d164859 q = 1) : d164859 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164868 q = 1) : d164868 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d164897 q = 1) : d164897 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d164936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15003 q selected
    | true =>
      simp only [d164936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15004 q selected
  have h4 (q : Pattern) (selected : d164937 q = 1) : d166391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164937, d166391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164937, d166391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164952 q = 1) : d164952 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d164953 q = 1) : d166392 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164953, d166392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164953, d166392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164954 q = 1) : d166393 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164954, d166393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164954, d166393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164955 q = 1) : d166394 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164955, d166394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164955, d166394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164962 q = 1) : d164962 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d164967 q = 1) : d164967 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d164970 q = 1) : d164970 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d164973 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15006 q selected
    | true =>
      simp only [d164973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15007 q selected
  have h13 (q : Pattern) (selected : d164974 q = 1) : d166396 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164974, d166396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164974, d166396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164977 q = 1) : d164977 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d164978 q = 1) : d166397 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164978, d166397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d164978, d166397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164979 q = 1) : d166398 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164979, d166398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164979, d166398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d164980 q = 1) : d166399 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164980, d166399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d164980, d166399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d164981 q = 1) : d166400 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164981, d166400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d164981, d166400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro15009 (p : Pattern) (selected : d165006 p = 1) : d166407 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164970 q = 1) : d164970 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d164973 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15006 q selected
    | true =>
      simp only [d164973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15007 q selected
  have h3 (q : Pattern) (selected : d164974 q = 1) : d166396 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164974, d166396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164974, d166396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164977 q = 1) : d164977 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d164978 q = 1) : d166397 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164978, d166397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164978, d166397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d165004 q = 1) : d166405 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d165004, d166405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165004, d166405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d165005 q = 1) : d166406 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d165005, d166406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165005, d166406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d165006 q = 1) : d166407 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d165006, d166407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165006, d166407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15010 (p : Pattern) (selected : d165015 p = 1) : d166414 p = 1 := by
  have h0 (q : Pattern) (selected : d164851 q = 1) : d164851 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164982 q = 1) : d166401 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164982, d166401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15005 q selected
    | true =>
      simp only [d164982, d166401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15008 q selected
  have h2 (q : Pattern) (selected : d165000 q = 1) : d165000 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d165001 q = 1) : d166402 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d165001, d166402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165001, d166402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d165002 q = 1) : d166403 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d165002, d166403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165002, d166403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d165003 q = 1) : d166404 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d165003, d166404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165003, d166404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d165007 q = 1) : d166408 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d165007, d166408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165007, d166408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15009 q selected
  have h8 (q : Pattern) (selected : d165009 q = 1) : d165009 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d165010 q = 1) : d166409 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d165010, d166409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d165010, d166409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d165011 q = 1) : d166410 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d165011, d166410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d165011, d166410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d165012 q = 1) : d166411 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d165012, d166411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d165012, d166411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d165013 q = 1) : d166412 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d165013, d166412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d165013, d166412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d165014 q = 1) : d166413 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d165014, d166413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d165014, d166413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d165015 q = 1) : d166414 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d165015, d166414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d165015, d166414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro15011 (p : Pattern) (selected : d165021 p = 1) : d166420 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d165016 q = 1) : d166415 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d165016, d166415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165016, d166415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15010 q selected
  have h2 (q : Pattern) (selected : d165017 q = 1) : d166416 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d165017, d166416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165017, d166416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d165018 q = 1) : d166417 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d165018, d166417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165018, d166417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d165019 q = 1) : d166418 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d165019, d166418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165019, d166418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d165020 q = 1) : d166419 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d165020, d166419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165020, d166419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d165021 q = 1) : d166420 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d165021, d166420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165021, d166420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15012 (p : Pattern) (selected : d165027 p = 1) : d166426 p = 1 := by
  have h0 (q : Pattern) (selected : d164141 q = 1) : d166291 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d164141, d166291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14940 q selected
    | true =>
      simp only [d164141, d166291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14952 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d164330 q = 1) : d166322 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d164330, d166322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164330, d166322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14966 q selected
  have h3 (q : Pattern) (selected : d164331 q = 1) : d166323 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d164331, d166323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164331, d166323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164560 q = 1) : d166354 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d164560, d166354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164560, d166354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14981 q selected
  have h5 (q : Pattern) (selected : d164561 q = 1) : d166355 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d164561, d166355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164561, d166355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164562 q = 1) : d166356 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d164562, d166356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164562, d166356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164791 q = 1) : d166387 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d164791, d166387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164791, d166387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14996 q selected
  have h8 (q : Pattern) (selected : d164792 q = 1) : d166388 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d164792, d166388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164792, d166388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164793 q = 1) : d166389 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d164793, d166389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164793, d166389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164794 q = 1) : d166390 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d164794, d166390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164794, d166390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d165022 q = 1) : d166421 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d165022, d166421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165022, d166421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15011 q selected
  have h12 (q : Pattern) (selected : d165023 q = 1) : d166422 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d165023, d166422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165023, d166422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d165024 q = 1) : d166423 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d165024, d166423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165024, d166423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d165025 q = 1) : d166424 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d165025, d166424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165025, d166424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d165026 q = 1) : d166425 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d165026, d166425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d165026, d166425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d165027 q = 1) : d166426 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d165027, d166426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d165027, d166426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro15013 (p : Pattern) (selected : d165033 p = 1) : d166432 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d165028 q = 1) : d166427 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d165028, d166427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15012 q selected
    | true =>
      simp only [d165028, d166427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165029 q = 1) : d166428 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d165029, d166428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165029, d166428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d165030 q = 1) : d166429 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d165030, d166429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d165030, d166429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165031 q = 1) : d166430 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d165031, d166430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165031, d166430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d165032 q = 1) : d166431 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d165032, d166431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165032, d166431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d165033 q = 1) : d166432 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d165033, d166432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d165033, d166432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15014 (p : Pattern) (selected : d165039 p = 1) : d166438 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d165034 q = 1) : d166433 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d165034, d166433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15013 q selected
    | true =>
      simp only [d165034, d166433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165035 q = 1) : d166434 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d165035, d166434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165035, d166434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d165036 q = 1) : d166435 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d165036, d166435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d165036, d166435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165037 q = 1) : d166436 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d165037, d166436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165037, d166436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d165038 q = 1) : d166437 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d165038, d166437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165038, d166437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d165039 q = 1) : d166438 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d165039, d166438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d165039, d166438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15015 (p : Pattern) (selected : d165045 p = 1) : d166444 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d165040 q = 1) : d166439 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d165040, d166439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15014 q selected
    | true =>
      simp only [d165040, d166439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165041 q = 1) : d166440 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d165041, d166440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165041, d166440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d165042 q = 1) : d166441 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d165042, d166441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d165042, d166441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165043 q = 1) : d166442 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d165043, d166442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165043, d166442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d165044 q = 1) : d166443 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d165044, d166443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165044, d166443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d165045 q = 1) : d166444 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d165045, d166444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d165045, d166444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15016 (p : Pattern) (selected : d165051 p = 1) : d166450 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d165046 q = 1) : d166445 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d165046, d166445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15015 q selected
    | true =>
      simp only [d165046, d166445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165047 q = 1) : d166446 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d165047, d166446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165047, d166446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d165048 q = 1) : d166447 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d165048, d166447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d165048, d166447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165049 q = 1) : d166448 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d165049, d166448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165049, d166448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d165050 q = 1) : d166449 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d165050, d166449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165050, d166449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d165051 q = 1) : d166450 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d165051, d166450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d165051, d166450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15017 (p : Pattern) (selected : d165057 p = 1) : d166456 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d165052 q = 1) : d166451 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d165052, d166451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15016 q selected
    | true =>
      simp only [d165052, d166451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165053 q = 1) : d166452 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d165053, d166452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165053, d166452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d165054 q = 1) : d166453 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d165054, d166453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d165054, d166453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165055 q = 1) : d166454 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d165055, d166454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165055, d166454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d165056 q = 1) : d166455 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d165056, d166455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165056, d166455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d165057 q = 1) : d166456 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d165057, d166456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d165057, d166456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15018 (p : Pattern) (selected : d165063 p = 1) : d166462 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d165058 q = 1) : d166457 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d165058, d166457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15017 q selected
    | true =>
      simp only [d165058, d166457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165059 q = 1) : d166458 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d165059, d166458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165059, d166458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d165060 q = 1) : d166459 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d165060, d166459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d165060, d166459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165061 q = 1) : d166460 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d165061, d166460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165061, d166460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d165062 q = 1) : d166461 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d165062, d166461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165062, d166461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d165063 q = 1) : d166462 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d165063, d166462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d165063, d166462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15019 (p : Pattern) (selected : d165069 p = 1) : d166468 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d165064 q = 1) : d166463 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d165064, d166463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15018 q selected
    | true =>
      simp only [d165064, d166463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165065 q = 1) : d166464 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d165065, d166464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165065, d166464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d165066 q = 1) : d166465 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d165066, d166465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d165066, d166465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165067 q = 1) : d166466 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d165067, d166466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165067, d166466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d165068 q = 1) : d166467 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d165068, d166467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165068, d166467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d165069 q = 1) : d166468 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d165069, d166468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d165069, d166468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15020 (p : Pattern) (selected : d12495 p = 0) : d112929 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9382 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9384 q = 0) : d101017 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12493 q = 0) : d112927 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12494 q = 0) : d112928 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d27 q = 0) : d51879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d28 q = 0) : d51880 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d12495 q = 0) : d112929 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d112929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12495, d112929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15021 (p : Pattern) (selected : d166473 p = 0) : d167243 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135651 q = 0) : d137050 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135651, d137050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135651, d137050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6044 q selected
  have h2 (q : Pattern) (selected : d135652 q = 0) : d137051 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135652, d137051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135652, d137051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166469 q = 0) : d167239 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166469, d167239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166469, d167239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15020 q selected
  have h4 (q : Pattern) (selected : d166470 q = 0) : d167240 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166470, d167240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166470, d167240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166471 q = 0) : d167241 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166471, d167241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166471, d167241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135522 q = 0) : d136947 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135522, d136947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135522, d136947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6017 q selected
  have h7 (q : Pattern) (selected : d135523 q = 0) : d136948 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135523, d136948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135523, d136948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135433 q = 0) : d136858 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135433, d136858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135433, d136858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6001 q selected
  have h9 (q : Pattern) (selected : d135434 q = 0) : d136859 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135434, d136859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135434, d136859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135524 q = 0) : d136949 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135524, d136949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135524, d136949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166472 q = 0) : d167242 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166472, d167242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166472, d167242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d166473 q = 0) : d167243 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166473, d167243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166473, d167243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro15022 (p : Pattern) (selected : d166479 p = 0) : d167249 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166474 q = 0) : d167244 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166474, d167244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15021 q selected
    | true =>
      simp only [d166474, d167244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166475 q = 0) : d167245 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166475, d167245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166475, d167245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135527 q = 0) : d136952 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11602 q selected
    | true =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135528 q = 0) : d136953 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166476 q = 0) : d167246 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166476, d167246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166476, d167246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166477 q = 0) : d167247 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166477, d167247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166477, d167247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166478 q = 0) : d167248 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166478, d167248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166478, d167248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166479 q = 0) : d167249 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166479, d167249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166479, d167249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15023 (p : Pattern) (selected : d166485 p = 0) : d167255 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135641 q = 0) : d137040 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135641, d137040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11623 q selected
    | true =>
      simp only [d135641, d137040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11600 q selected
  have h2 (q : Pattern) (selected : d135642 q = 0) : d137041 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135642, d137041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135642, d137041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135643 q = 0) : d137042 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135643, d137042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135643, d137042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135644 q = 0) : d137043 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135644, d137043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135644, d137043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135648 q = 0) : d137047 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135648, d137047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11624 q selected
    | true =>
      simp only [d135648, d137047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11601 q selected
  have h6 (q : Pattern) (selected : d135649 q = 0) : d137048 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135649, d137048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135649, d137048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135650 q = 0) : d137049 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135650, d137049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135650, d137049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166480 q = 0) : d167250 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166480, d167250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15022 q selected
    | true =>
      simp only [d166480, d167250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11603 q selected
  have h9 (q : Pattern) (selected : d135674 q = 0) : d136958 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135674, d136958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11628 q selected
    | true =>
      simp only [d135674, d136958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11605 q selected
  have h10 (q : Pattern) (selected : d166481 q = 0) : d167251 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166481, d167251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d166481, d167251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d135680 q = 0) : d137067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135680, d137067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11629 q selected
    | true =>
      simp only [d135680, d137067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d135681 q = 0) : d137068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135681, d137068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d135681, d137068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d166482 q = 0) : d167252 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166482, d167252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166482, d167252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d166483 q = 0) : d167253 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166483, d167253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166483, d167253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d166484 q = 0) : d167254 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166484, d167254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166484, d167254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d166485 q = 0) : d167255 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166485, d167255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166485, d167255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro15024 (p : Pattern) (selected : d166486 p = 0) : d167256 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166474 q = 0) : d167244 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166474, d167244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15021 q selected
    | true =>
      simp only [d166474, d167244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166475 q = 0) : d167245 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166475, d167245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166475, d167245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135527 q = 0) : d136952 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11602 q selected
    | true =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135528 q = 0) : d136953 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166476 q = 0) : d167246 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166476, d167246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166476, d167246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166477 q = 0) : d167247 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166477, d167247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166477, d167247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166478 q = 0) : d167248 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166478, d167248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166478, d167248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166486 q = 0) : d167256 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166486, d167256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166486, d167256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15025 (p : Pattern) (selected : d166492 p = 0) : d167262 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135641 q = 0) : d137040 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135641, d137040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11623 q selected
    | true =>
      simp only [d135641, d137040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11600 q selected
  have h2 (q : Pattern) (selected : d135642 q = 0) : d137041 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135642, d137041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135642, d137041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135643 q = 0) : d137042 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135643, d137042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135643, d137042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135644 q = 0) : d137043 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135644, d137043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135644, d137043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135648 q = 0) : d137047 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135648, d137047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11624 q selected
    | true =>
      simp only [d135648, d137047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11601 q selected
  have h6 (q : Pattern) (selected : d135649 q = 0) : d137048 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135649, d137048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135649, d137048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135650 q = 0) : d137049 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135650, d137049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135650, d137049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166480 q = 0) : d167250 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166480, d167250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15022 q selected
    | true =>
      simp only [d166480, d167250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11603 q selected
  have h9 (q : Pattern) (selected : d135674 q = 0) : d136958 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135674, d136958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11628 q selected
    | true =>
      simp only [d135674, d136958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11605 q selected
  have h10 (q : Pattern) (selected : d166481 q = 0) : d167251 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166481, d167251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d166481, d167251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d135680 q = 0) : d137067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135680, d137067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11629 q selected
    | true =>
      simp only [d135680, d137067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d135681 q = 0) : d137068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135681, d137068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d135681, d137068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d166482 q = 0) : d167252 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166482, d167252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166482, d167252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d166483 q = 0) : d167253 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166483, d167253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166483, d167253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d166484 q = 0) : d167254 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166484, d167254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166484, d167254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d135687 q = 0) : d137074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135687, d137074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11631 q selected
    | true =>
      simp only [d135687, d137074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11607 q selected
  have h17 (q : Pattern) (selected : d135688 q = 0) : d137075 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135688, d137075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135688, d137075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d135689 q = 0) : d137076 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135689, d137076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d135689, d137076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d135690 q = 0) : d137077 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135690, d137077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135690, d137077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d135692 q = 0) : d137079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135692, d137079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11632 q selected
    | true =>
      simp only [d135692, d137079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11608 q selected
  have h21 (q : Pattern) (selected : d135693 q = 0) : d137080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135693, d137080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135693, d137080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d135694 q = 0) : d137081 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135694, d137081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d135694, d137081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d166487 q = 0) : d167257 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166487, d167257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15024 q selected
    | true =>
      simp only [d166487, d167257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11609 q selected
  have h24 (q : Pattern) (selected : d135698 q = 0) : d136974 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135698, d136974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11634 q selected
    | true =>
      simp only [d135698, d136974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11610 q selected
  have h25 (q : Pattern) (selected : d166488 q = 0) : d167258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166488, d167258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d166488, d167258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d135701 q = 0) : d137086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135701, d137086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11635 q selected
    | true =>
      simp only [d135701, d137086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d135702 q = 0) : d137087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135702, d137087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d135702, d137087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d166489 q = 0) : d167259 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166489, d167259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d166489, d167259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d166490 q = 0) : d167260 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166490, d167260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d166490, d167260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d166491 q = 0) : d167261 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166491, d167261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d166491, d167261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d166492 q = 0) : d167262 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166492, d167262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d166492, d167262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro15026 (p : Pattern) (selected : d166499 p = 0) : d167269 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166487 q = 0) : d167257 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166487, d167257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15024 q selected
    | true =>
      simp only [d166487, d167257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11609 q selected
  have h2 (q : Pattern) (selected : d135698 q = 0) : d136974 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135698, d136974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11634 q selected
    | true =>
      simp only [d135698, d136974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11610 q selected
  have h3 (q : Pattern) (selected : d166488 q = 0) : d167258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166488, d167258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166488, d167258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d135701 q = 0) : d137086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135701, d137086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11635 q selected
    | true =>
      simp only [d135701, d137086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135702 q = 0) : d137087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135702, d137087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135702, d137087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d166489 q = 0) : d167259 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166489, d167259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166489, d167259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166497 q = 0) : d167267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166497, d167267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166497, d167267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166498 q = 0) : d167268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166498, d167268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166498, d167268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d166499 q = 0) : d167269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166499, d167269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166499, d167269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15027 (p : Pattern) (selected : d12603 p = 0) : d113011 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12599 q = 0) : d113007 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
  have h2 (q : Pattern) (selected : d9382 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12600 q = 0) : d113008 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9384 q = 0) : d101017 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12601 q = 0) : d113009 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d113009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12601, d113009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12602 q = 0) : d113010 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d113010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12602, d113010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d66 q = 0) : d51918 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
  have h8 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d67 q = 0) : d51919 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d68 q = 0) : d51920 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d69 q = 0) : d51921 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d12603 q = 0) : d113011 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d113011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12603, d113011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro15028 (p : Pattern) (selected : d166509 p = 0) : d167279 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135723 q = 0) : d137108 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135723, d137108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135723, d137108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6064 q selected
  have h2 (q : Pattern) (selected : d135724 q = 0) : d137109 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135724, d137109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135724, d137109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166505 q = 0) : d167275 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166505, d167275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166505, d167275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15027 q selected
  have h4 (q : Pattern) (selected : d166506 q = 0) : d167276 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166506, d167276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166506, d167276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166507 q = 0) : d167277 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166507, d167277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166507, d167277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135583 q = 0) : d136994 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135583, d136994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135583, d136994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6031 q selected
  have h7 (q : Pattern) (selected : d135584 q = 0) : d136995 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135584, d136995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135584, d136995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135467 q = 0) : d136892 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135467, d136892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135467, d136892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6008 q selected
  have h9 (q : Pattern) (selected : d135468 q = 0) : d136893 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135468, d136893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135468, d136893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135585 q = 0) : d136996 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135585, d136996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135585, d136996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166508 q = 0) : d167278 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166508, d167278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166508, d167278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d166509 q = 0) : d167279 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166509, d167279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166509, d167279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro15029 (p : Pattern) (selected : d166515 p = 0) : d167285 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166510 q = 0) : d167280 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166510, d167280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15028 q selected
    | true =>
      simp only [d166510, d167280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166511 q = 0) : d167281 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166511, d167281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166511, d167281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135588 q = 0) : d136999 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135588, d136999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11614 q selected
    | true =>
      simp only [d135588, d136999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135589 q = 0) : d137000 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135589, d137000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135589, d137000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166512 q = 0) : d167282 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166512, d167282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166512, d167282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166513 q = 0) : d167283 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166513, d167283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166513, d167283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166514 q = 0) : d167284 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166514, d167284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166514, d167284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166515 q = 0) : d167285 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166515, d167285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166515, d167285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15030 (p : Pattern) (selected : d166521 p = 0) : d167291 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166516 q = 0) : d167286 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166516, d167286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15029 q selected
    | true =>
      simp only [d166516, d167286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11615 q selected
  have h2 (q : Pattern) (selected : d135746 q = 0) : d137005 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135746, d137005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11643 q selected
    | true =>
      simp only [d135746, d137005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11617 q selected
  have h3 (q : Pattern) (selected : d166517 q = 0) : d167287 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166517, d167287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166517, d167287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d135752 q = 0) : d137125 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135752, d137125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11644 q selected
    | true =>
      simp only [d135752, d137125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135753 q = 0) : d137126 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135753, d137126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135753, d137126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d166518 q = 0) : d167288 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166518, d167288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166518, d167288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166519 q = 0) : d167289 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166519, d167289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166519, d167289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166520 q = 0) : d167290 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166520, d167290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166520, d167290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d166521 q = 0) : d167291 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166521, d167291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166521, d167291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15031 (p : Pattern) (selected : d166527 p = 0) : d167297 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135629 q = 0) : d137028 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135629, d137028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135629, d137028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11621 q selected
  have h2 (q : Pattern) (selected : d135630 q = 0) : d137029 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135630, d137029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135630, d137029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d135636 q = 0) : d137035 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135636, d137035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11621 q selected
    | true =>
      simp only [d135636, d137035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11622 q selected
  have h4 (q : Pattern) (selected : d135637 q = 0) : d137036 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135637, d137036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135637, d137036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135638 q = 0) : d137037 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135638, d137037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135638, d137037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166493 q = 0) : d167263 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166493, d167263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15023 q selected
    | true =>
      simp only [d166493, d167263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15025 q selected
  have h7 (q : Pattern) (selected : d135709 q = 0) : d137094 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135709, d137094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11637 q selected
    | true =>
      simp only [d135709, d137094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11599 q selected
  have h8 (q : Pattern) (selected : d166494 q = 0) : d167264 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166494, d167264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166494, d167264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d166495 q = 0) : d167265 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166495, d167265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d166495, d167265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d166496 q = 0) : d167266 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166496, d167266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166496, d167266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166500 q = 0) : d167270 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166500, d167270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166500, d167270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15026 q selected
  have h12 (q : Pattern) (selected : d135718 q = 0) : d137103 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135718, d137103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135718, d137103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11639 q selected
  have h13 (q : Pattern) (selected : d166501 q = 0) : d167271 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166501, d167271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166501, d167271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d166502 q = 0) : d167272 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166502, d167272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d166502, d167272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d166503 q = 0) : d167273 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166503, d167273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d166503, d167273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d166504 q = 0) : d167274 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d166504, d167274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166504, d167274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d166522 q = 0) : d167292 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166522, d167292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166522, d167292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15030 q selected
  have h18 (q : Pattern) (selected : d135764 q = 0) : d137137 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135764, d137137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135764, d137137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11646 q selected
  have h19 (q : Pattern) (selected : d166523 q = 0) : d167293 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166523, d167293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d166523, d167293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d166524 q = 0) : d167294 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166524, d167294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d166524, d167294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d166525 q = 0) : d167295 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166525, d167295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d166525, d167295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d166526 q = 0) : d167296 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d166526, d167296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d166526, d167296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d166527 q = 0) : d167297 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d166527, d167297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d166527, d167297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro15032 (p : Pattern) (selected : d166533 p = 0) : d167303 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166528 q = 0) : d167298 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d166528, d167298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166528, d167298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15031 q selected
  have h2 (q : Pattern) (selected : d166529 q = 0) : d167299 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d166529, d167299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166529, d167299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166530 q = 0) : d167300 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d166530, d167300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166530, d167300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166531 q = 0) : d167301 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d166531, d167301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166531, d167301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166532 q = 0) : d167302 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d166532, d167302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166532, d167302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166533 q = 0) : d167303 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d166533, d167303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166533, d167303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15033 (p : Pattern) (selected : d12750 p = 0) : d113136 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9470 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12748 q = 0) : d113134 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12749 q = 0) : d113135 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d753 q = 0) : d52430 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d754 q = 0) : d52431 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d12750 q = 0) : d113136 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d113136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12750, d113136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15034 (p : Pattern) (selected : d166539 p = 0) : d167309 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135835 q = 0) : d137208 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135835, d137208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135835, d137208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6091 q selected
  have h2 (q : Pattern) (selected : d135836 q = 0) : d137209 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135836, d137209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135836, d137209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166535 q = 0) : d167305 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166535, d167305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166535, d167305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15033 q selected
  have h4 (q : Pattern) (selected : d166536 q = 0) : d167306 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166536, d167306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166536, d167306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166537 q = 0) : d167307 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166537, d167307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166537, d167307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135777 q = 0) : d137150 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135777, d137150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135777, d137150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6077 q selected
  have h7 (q : Pattern) (selected : d135778 q = 0) : d137151 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135778, d137151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135778, d137151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135779 q = 0) : d137152 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135779, d137152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135779, d137152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6078 q selected
  have h9 (q : Pattern) (selected : d135780 q = 0) : d137153 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135780, d137153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135780, d137153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135781 q = 0) : d137154 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135781, d137154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135781, d137154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166538 q = 0) : d167308 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166538, d167308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166538, d167308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d166539 q = 0) : d167309 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166539, d167309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166539, d167309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro15035 (p : Pattern) (selected : d166545 p = 0) : d167315 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166540 q = 0) : d167310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166540, d167310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15034 q selected
    | true =>
      simp only [d166540, d167310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166541 q = 0) : d167311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166541, d167311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166541, d167311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135785 q = 0) : d137158 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11649 q selected
    | true =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135786 q = 0) : d137159 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166542 q = 0) : d167312 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166542, d167312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166542, d167312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166543 q = 0) : d167313 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166543, d167313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166543, d167313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166544 q = 0) : d167314 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166544, d167314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166544, d167314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166545 q = 0) : d167315 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166545, d167315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166545, d167315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15036 (p : Pattern) (selected : d166551 p = 0) : d167321 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135785 q = 0) : d137158 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11649 q selected
    | true =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135786 q = 0) : d137159 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166548 q = 0) : d167318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166548, d167318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166548, d167318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166549 q = 0) : d167319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166549, d167319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166549, d167319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d166550 q = 0) : d167320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166550, d167320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166550, d167320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d166551 q = 0) : d167321 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166551, d167321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166551, d167321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15037 (p : Pattern) (selected : d166557 p = 0) : d167327 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135822 q = 0) : d137195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135822, d137195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11657 q selected
    | true =>
      simp only [d135822, d137195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11658 q selected
  have h2 (q : Pattern) (selected : d135823 q = 0) : d137196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135823, d137196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135823, d137196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135824 q = 0) : d137197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135824, d137197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135824, d137197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135825 q = 0) : d137198 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135825, d137198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135825, d137198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135832 q = 0) : d137205 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135832, d137205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11659 q selected
    | true =>
      simp only [d135832, d137205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11660 q selected
  have h6 (q : Pattern) (selected : d135833 q = 0) : d137206 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135833, d137206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135833, d137206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135834 q = 0) : d137207 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135834, d137207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135834, d137207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166546 q = 0) : d167316 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166546, d167316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15035 q selected
    | true =>
      simp only [d166546, d167316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11651 q selected
  have h9 (q : Pattern) (selected : d135869 q = 0) : d137172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135869, d137172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11665 q selected
    | true =>
      simp only [d135869, d137172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11666 q selected
  have h10 (q : Pattern) (selected : d166547 q = 0) : d167317 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166547, d167317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d166547, d167317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166552 q = 0) : d167322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166552, d167322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15036 q selected
    | true =>
      simp only [d166552, d167322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d166553 q = 0) : d167323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166553, d167323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166553, d167323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d166554 q = 0) : d167324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166554, d167324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166554, d167324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d166555 q = 0) : d167325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166555, d167325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166555, d167325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d166556 q = 0) : d167326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166556, d167326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166556, d167326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d166557 q = 0) : d167327 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166557, d167327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166557, d167327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro15038 (p : Pattern) (selected : d166558 p = 0) : d167328 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166540 q = 0) : d167310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166540, d167310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15034 q selected
    | true =>
      simp only [d166540, d167310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166541 q = 0) : d167311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166541, d167311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166541, d167311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135785 q = 0) : d137158 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11649 q selected
    | true =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135786 q = 0) : d137159 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166542 q = 0) : d167312 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166542, d167312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166542, d167312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166543 q = 0) : d167313 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166543, d167313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166543, d167313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166544 q = 0) : d167314 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166544, d167314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166544, d167314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166558 q = 0) : d167328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166558, d167328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166558, d167328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15039 (p : Pattern) (selected : d166561 p = 0) : d167331 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135785 q = 0) : d137158 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11649 q selected
    | true =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135786 q = 0) : d137159 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166548 q = 0) : d167318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166548, d167318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166548, d167318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166549 q = 0) : d167319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166549, d167319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166549, d167319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d166550 q = 0) : d167320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166550, d167320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166550, d167320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d166561 q = 0) : d167331 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166561, d167331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166561, d167331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15040 (p : Pattern) (selected : d166567 p = 0) : d167337 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135822 q = 0) : d137195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135822, d137195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11657 q selected
    | true =>
      simp only [d135822, d137195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11658 q selected
  have h2 (q : Pattern) (selected : d135823 q = 0) : d137196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135823, d137196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135823, d137196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135824 q = 0) : d137197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135824, d137197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135824, d137197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135825 q = 0) : d137198 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135825, d137198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135825, d137198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135832 q = 0) : d137205 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135832, d137205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11659 q selected
    | true =>
      simp only [d135832, d137205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11660 q selected
  have h6 (q : Pattern) (selected : d135833 q = 0) : d137206 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135833, d137206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135833, d137206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135834 q = 0) : d137207 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135834, d137207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135834, d137207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166546 q = 0) : d167316 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166546, d167316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15035 q selected
    | true =>
      simp only [d166546, d167316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11651 q selected
  have h9 (q : Pattern) (selected : d135869 q = 0) : d137172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135869, d137172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11665 q selected
    | true =>
      simp only [d135869, d137172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11666 q selected
  have h10 (q : Pattern) (selected : d166547 q = 0) : d167317 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166547, d167317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d166547, d167317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166552 q = 0) : d167322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166552, d167322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15036 q selected
    | true =>
      simp only [d166552, d167322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d166553 q = 0) : d167323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166553, d167323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166553, d167323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d166554 q = 0) : d167324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166554, d167324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166554, d167324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d166555 q = 0) : d167325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166555, d167325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166555, d167325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d166556 q = 0) : d167326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166556, d167326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166556, d167326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d135890 q = 0) : d137240 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135890, d137240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11671 q selected
    | true =>
      simp only [d135890, d137240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11672 q selected
  have h17 (q : Pattern) (selected : d135891 q = 0) : d137241 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135891, d137241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135891, d137241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d135892 q = 0) : d137242 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135892, d137242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d135892, d137242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d135893 q = 0) : d137243 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135893, d137243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135893, d137243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d135896 q = 0) : d137246 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135896, d137246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11673 q selected
    | true =>
      simp only [d135896, d137246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11674 q selected
  have h21 (q : Pattern) (selected : d135897 q = 0) : d137247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135897, d137247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135897, d137247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d135898 q = 0) : d137248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135898, d137248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d135898, d137248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d166559 q = 0) : d167329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166559, d167329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15038 q selected
    | true =>
      simp only [d166559, d167329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11654 q selected
  have h24 (q : Pattern) (selected : d135903 q = 0) : d137182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135903, d137182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11676 q selected
    | true =>
      simp only [d135903, d137182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11677 q selected
  have h25 (q : Pattern) (selected : d166560 q = 0) : d167330 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166560, d167330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d166560, d167330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d166562 q = 0) : d167332 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166562, d167332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15039 q selected
    | true =>
      simp only [d166562, d167332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d166563 q = 0) : d167333 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166563, d167333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d166563, d167333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d166564 q = 0) : d167334 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166564, d167334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d166564, d167334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d166565 q = 0) : d167335 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166565, d167335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d166565, d167335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d166566 q = 0) : d167336 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166566, d167336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d166566, d167336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d166567 q = 0) : d167337 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166567, d167337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d166567, d167337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro15041 (p : Pattern) (selected : d166574 p = 0) : d167344 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166559 q = 0) : d167329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166559, d167329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15038 q selected
    | true =>
      simp only [d166559, d167329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11654 q selected
  have h2 (q : Pattern) (selected : d135903 q = 0) : d137182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135903, d137182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11676 q selected
    | true =>
      simp only [d135903, d137182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11677 q selected
  have h3 (q : Pattern) (selected : d166560 q = 0) : d167330 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166560, d167330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166560, d167330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166562 q = 0) : d167332 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166562, d167332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15039 q selected
    | true =>
      simp only [d166562, d167332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d166563 q = 0) : d167333 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166563, d167333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166563, d167333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d166564 q = 0) : d167334 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166564, d167334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166564, d167334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166572 q = 0) : d167342 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166572, d167342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166572, d167342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166573 q = 0) : d167343 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166573, d167343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166573, d167343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d166574 q = 0) : d167344 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166574, d167344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166574, d167344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15042 (p : Pattern) (selected : d12862 p = 0) : d113218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12858 q = 0) : d113214 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
  have h2 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12859 q = 0) : d113215 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9470 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12860 q = 0) : d113216 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12861 q = 0) : d113217 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d113217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12861, d113217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d971 q = 0) : d52590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
  have h8 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d972 q = 0) : d52591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d973 q = 0) : d52592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d974 q = 0) : d52593 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d12862 q = 0) : d113218 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d113218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12862, d113218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro15043 (p : Pattern) (selected : d166584 p = 0) : d167354 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135939 q = 0) : d137286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135939, d137286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135939, d137286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6118 q selected
  have h2 (q : Pattern) (selected : d135940 q = 0) : d137287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135940, d137287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135940, d137287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166580 q = 0) : d167350 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166580, d167350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166580, d167350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15042 q selected
  have h4 (q : Pattern) (selected : d166581 q = 0) : d167351 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166581, d167351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166581, d167351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166582 q = 0) : d167352 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166582, d167352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166582, d167352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135941 q = 0) : d137288 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135941, d137288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135941, d137288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6119 q selected
  have h7 (q : Pattern) (selected : d135942 q = 0) : d137289 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135942, d137289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135942, d137289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135944 q = 0) : d137291 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135944, d137291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135944, d137291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6120 q selected
  have h9 (q : Pattern) (selected : d135945 q = 0) : d137292 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135945, d137292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135945, d137292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135946 q = 0) : d137293 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135946, d137293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135946, d137293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166583 q = 0) : d167353 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166583, d167353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166583, d167353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d166584 q = 0) : d167354 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166584, d167354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166584, d167354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro15044 (p : Pattern) (selected : d166590 p = 0) : d167360 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166585 q = 0) : d167355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166585, d167355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15043 q selected
    | true =>
      simp only [d166585, d167355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166586 q = 0) : d167356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166586, d167356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166586, d167356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135954 q = 0) : d137301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135954, d137301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11685 q selected
    | true =>
      simp only [d135954, d137301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135955 q = 0) : d137302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135955, d137302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135955, d137302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166587 q = 0) : d167357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166587, d167357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166587, d167357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166588 q = 0) : d167358 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166588, d167358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166588, d167358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166589 q = 0) : d167359 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166589, d167359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166589, d167359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166590 q = 0) : d167360 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166590, d167360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166590, d167360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15045 (p : Pattern) (selected : d166596 p = 0) : d167366 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135954 q = 0) : d137301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135954, d137301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11685 q selected
    | true =>
      simp only [d135954, d137301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135955 q = 0) : d137302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135955, d137302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135955, d137302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166593 q = 0) : d167363 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166593, d167363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166593, d167363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166594 q = 0) : d167364 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166594, d167364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166594, d167364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d166595 q = 0) : d167365 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166595, d167365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166595, d167365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d166596 q = 0) : d167366 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166596, d167366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166596, d167366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15046 (p : Pattern) (selected : d166602 p = 0) : d167372 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166591 q = 0) : d167361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166591, d167361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15044 q selected
    | true =>
      simp only [d166591, d167361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11688 q selected
  have h2 (q : Pattern) (selected : d135991 q = 0) : d137320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135991, d137320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11691 q selected
    | true =>
      simp only [d135991, d137320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11692 q selected
  have h3 (q : Pattern) (selected : d166592 q = 0) : d167362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166592, d167362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166592, d167362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166597 q = 0) : d167367 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166597, d167367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15045 q selected
    | true =>
      simp only [d166597, d167367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d166598 q = 0) : d167368 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166598, d167368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166598, d167368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d166599 q = 0) : d167369 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166599, d167369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166599, d167369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166600 q = 0) : d167370 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166600, d167370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166600, d167370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166601 q = 0) : d167371 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166601, d167371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166601, d167371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d166602 q = 0) : d167372 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166602, d167372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166602, d167372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15047 (p : Pattern) (selected : d166608 p = 0) : d167378 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135805 q = 0) : d137178 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135805, d137178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135805, d137178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11653 q selected
  have h2 (q : Pattern) (selected : d135806 q = 0) : d137179 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135806, d137179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135806, d137179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d135815 q = 0) : d137188 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135815, d137188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11653 q selected
    | true =>
      simp only [d135815, d137188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11656 q selected
  have h4 (q : Pattern) (selected : d135816 q = 0) : d137189 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135816, d137189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135816, d137189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135817 q = 0) : d137190 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135817, d137190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135817, d137190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166568 q = 0) : d167338 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166568, d167338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15037 q selected
    | true =>
      simp only [d166568, d167338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15040 q selected
  have h7 (q : Pattern) (selected : d135925 q = 0) : d137272 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135925, d137272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11680 q selected
    | true =>
      simp only [d135925, d137272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11681 q selected
  have h8 (q : Pattern) (selected : d166569 q = 0) : d167339 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166569, d167339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166569, d167339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d166570 q = 0) : d167340 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166570, d167340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d166570, d167340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d166571 q = 0) : d167341 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166571, d167341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166571, d167341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166575 q = 0) : d167345 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166575, d167345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166575, d167345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15041 q selected
  have h12 (q : Pattern) (selected : d135934 q = 0) : d137281 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135934, d137281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135934, d137281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11683 q selected
  have h13 (q : Pattern) (selected : d166576 q = 0) : d167346 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166576, d167346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166576, d167346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d166577 q = 0) : d167347 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166577, d167347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d166577, d167347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d166578 q = 0) : d167348 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166578, d167348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d166578, d167348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d166579 q = 0) : d167349 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d166579, d167349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166579, d167349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d166603 q = 0) : d167373 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166603, d167373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166603, d167373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15046 q selected
  have h18 (q : Pattern) (selected : d136021 q = 0) : d137346 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136021, d137346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136021, d137346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11698 q selected
  have h19 (q : Pattern) (selected : d166604 q = 0) : d167374 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166604, d167374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d166604, d167374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d166605 q = 0) : d167375 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166605, d167375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d166605, d167375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d166606 q = 0) : d167376 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166606, d167376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d166606, d167376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d166607 q = 0) : d167377 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d166607, d167377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d166607, d167377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d166608 q = 0) : d167378 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d166608, d167378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d166608, d167378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro15048 (p : Pattern) (selected : d166614 p = 0) : d167384 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166609 q = 0) : d167379 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d166609, d167379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166609, d167379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15047 q selected
  have h2 (q : Pattern) (selected : d166610 q = 0) : d167380 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d166610, d167380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166610, d167380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166611 q = 0) : d167381 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d166611, d167381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166611, d167381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166612 q = 0) : d167382 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d166612, d167382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166612, d167382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166613 q = 0) : d167383 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d166613, d167383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166613, d167383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166614 q = 0) : d167384 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d166614, d167384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166614, d167384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15049 (p : Pattern) (selected : d5022 p = 0) : d69112 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5018 q = 0) : d69108 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2799 q selected
    | true =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d5019 q = 0) : d69109 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d5020 q = 0) : d69110 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5020, d69110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5020, d69110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5021 q = 0) : d69111 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5021, d69111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5021, d69111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d5022 q = 0) : d69112 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5022, d69112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d5022, d69112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro15050 (p : Pattern) (selected : d166621 p = 0) : d167391 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136035 q = 0) : d137360 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136035, d137360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136035, d137360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6139 q selected
  have h2 (q : Pattern) (selected : d136036 q = 0) : d137361 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136036, d137361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136036, d137361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166617 q = 0) : d167387 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166617, d167387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166617, d167387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15049 q selected
  have h4 (q : Pattern) (selected : d166618 q = 0) : d167388 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166618, d167388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166618, d167388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166619 q = 0) : d167389 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166619, d167389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166619, d167389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136037 q = 0) : d137362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136037, d137362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136037, d137362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6140 q selected
  have h7 (q : Pattern) (selected : d136038 q = 0) : d137363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136038, d137363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136038, d137363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136040 q = 0) : d137365 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136040, d137365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136040, d137365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d166620 q = 0) : d167390 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166620, d167390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166620, d167390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166621 q = 0) : d167391 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166621, d167391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166621, d167391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15051 (p : Pattern) (selected : d166627 p = 0) : d167397 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166622 q = 0) : d167392 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166622, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15050 q selected
    | true =>
      simp only [d166622, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166623 q = 0) : d167393 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166623, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166623, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166624 q = 0) : d167394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166624, d167394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166624, d167394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166625 q = 0) : d167395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166625, d167395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166625, d167395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166626 q = 0) : d167396 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166626, d167396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166626, d167396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166627 q = 0) : d167397 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166627, d167397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166627, d167397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15052 (p : Pattern) (selected : d166633 p = 0) : d167403 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166628 q = 0) : d167398 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166628, d167398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15051 q selected
    | true =>
      simp only [d166628, d167398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11704 q selected
  have h2 (q : Pattern) (selected : d166629 q = 0) : d167399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166629, d167399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166629, d167399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166630 q = 0) : d167400 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166630, d167400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166630, d167400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166631 q = 0) : d167401 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166631, d167401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166631, d167401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166632 q = 0) : d167402 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166632, d167402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166632, d167402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166633 q = 0) : d167403 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166633, d167403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166633, d167403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15053 (p : Pattern) (selected : d166636 p = 0) : d167406 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166622 q = 0) : d167392 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166622, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15050 q selected
    | true =>
      simp only [d166622, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166623 q = 0) : d167393 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166623, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166623, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166624 q = 0) : d167394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166624, d167394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166624, d167394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166625 q = 0) : d167395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166625, d167395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166625, d167395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166626 q = 0) : d167396 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166626, d167396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166626, d167396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166636 q = 0) : d167406 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166636, d167406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166636, d167406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15054 (p : Pattern) (selected : d166642 p = 0) : d167412 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166628 q = 0) : d167398 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166628, d167398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15051 q selected
    | true =>
      simp only [d166628, d167398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11704 q selected
  have h2 (q : Pattern) (selected : d166629 q = 0) : d167399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166629, d167399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166629, d167399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166630 q = 0) : d167400 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166630, d167400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166630, d167400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166631 q = 0) : d167401 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166631, d167401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166631, d167401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166632 q = 0) : d167402 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166632, d167402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166632, d167402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166637 q = 0) : d167407 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166637, d167407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15053 q selected
    | true =>
      simp only [d166637, d167407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11707 q selected
  have h7 (q : Pattern) (selected : d166638 q = 0) : d167408 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166638, d167408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166638, d167408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166639 q = 0) : d167409 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166639, d167409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166639, d167409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d166640 q = 0) : d167410 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166640, d167410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166640, d167410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166641 q = 0) : d167411 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166641, d167411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166641, d167411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166642 q = 0) : d167412 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166642, d167412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166642, d167412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15055 (p : Pattern) (selected : d166647 p = 0) : d167417 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166622 q = 0) : d167392 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166622, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15050 q selected
    | true =>
      simp only [d166622, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166623 q = 0) : d167393 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166623, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166623, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166624 q = 0) : d167394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166624, d167394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166624, d167394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166625 q = 0) : d167395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166625, d167395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166625, d167395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166646 q = 0) : d167416 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166646, d167416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166646, d167416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166647 q = 0) : d167417 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166647, d167417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166647, d167417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15056 (p : Pattern) (selected : d166654 p = 0) : d167424 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166622 q = 0) : d167392 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166622, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15050 q selected
    | true =>
      simp only [d166622, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166623 q = 0) : d167393 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166623, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166623, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166624 q = 0) : d167394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166624, d167394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166624, d167394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166652 q = 0) : d167422 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166652, d167422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166652, d167422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166653 q = 0) : d167423 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166653, d167423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166653, d167423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166654 q = 0) : d167424 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166654, d167424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166654, d167424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15057 (p : Pattern) (selected : d13029 p = 0) : d113359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9814 q = 0) : d101335 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6677 q selected
    | true =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9816 q = 0) : d101337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, d101337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9816, d101337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13022 q = 0) : d113352 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13022, d113352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13022, d113352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13023 q = 0) : d113353 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13023, d113353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13023, d113353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13025 q = 0) : d113355 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8289 q selected
    | true =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13026 q = 0) : d113356 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13027 q = 0) : d113357 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13027, d113357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13027, d113357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13028 q = 0) : d113358 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13028, d113358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13028, d113358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13029 q = 0) : d113359 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13029, d113359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13029, d113359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15058 (p : Pattern) (selected : d166662 p = 0) : d167432 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136093 q = 0) : d137418 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136093, d137418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136093, d137418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6154 q selected
  have h2 (q : Pattern) (selected : d136094 q = 0) : d137419 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136094, d137419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136094, d137419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166658 q = 0) : d167428 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166658, d167428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166658, d167428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15057 q selected
  have h4 (q : Pattern) (selected : d166659 q = 0) : d167429 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166659, d167429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166659, d167429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166660 q = 0) : d167430 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166660, d167430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166660, d167430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136035 q = 0) : d137360 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136035, d137360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136035, d137360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6139 q selected
  have h7 (q : Pattern) (selected : d136036 q = 0) : d137361 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136036, d137361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136036, d137361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166617 q = 0) : d167387 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166617, d167387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166617, d167387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15049 q selected
  have h9 (q : Pattern) (selected : d166618 q = 0) : d167388 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166618, d167388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166618, d167388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166619 q = 0) : d167389 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166619, d167389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166619, d167389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166661 q = 0) : d167431 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166661, d167431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166661, d167431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d166662 q = 0) : d167432 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166662, d167432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166662, d167432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro15059 (p : Pattern) (selected : d166667 p = 0) : d167437 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136035 q = 0) : d137360 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136035, d137360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136035, d137360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6139 q selected
  have h2 (q : Pattern) (selected : d136036 q = 0) : d137361 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136036, d137361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136036, d137361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166617 q = 0) : d167387 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166617, d167387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166617, d167387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15049 q selected
  have h4 (q : Pattern) (selected : d166618 q = 0) : d167388 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166618, d167388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166618, d167388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166619 q = 0) : d167389 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166619, d167389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166619, d167389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166665 q = 0) : d167435 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166665, d167435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166665, d167435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166666 q = 0) : d167436 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166666, d167436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166666, d167436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166667 q = 0) : d167437 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166667, d167437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166667, d167437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15060 (p : Pattern) (selected : d166673 p = 0) : d167443 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166663 q = 0) : d167433 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166663, d167433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15058 q selected
    | true =>
      simp only [d166663, d167433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166664 q = 0) : d167434 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166664, d167434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166664, d167434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166668 q = 0) : d167438 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166668, d167438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15059 q selected
    | true =>
      simp only [d166668, d167438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166669 q = 0) : d167439 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166669, d167439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166669, d167439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166670 q = 0) : d167440 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166670, d167440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166670, d167440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166671 q = 0) : d167441 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166671, d167441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166671, d167441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166672 q = 0) : d167442 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166672, d167442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166672, d167442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166673 q = 0) : d167443 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166673, d167443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166673, d167443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15061 (p : Pattern) (selected : d166677 p = 0) : d167447 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166668 q = 0) : d167438 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166668, d167438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15059 q selected
    | true =>
      simp only [d166668, d167438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166669 q = 0) : d167439 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166669, d167439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166669, d167439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166674 q = 0) : d167444 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166674, d167444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166674, d167444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166675 q = 0) : d167445 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166675, d167445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166675, d167445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166676 q = 0) : d167446 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166676, d167446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166676, d167446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166677 q = 0) : d167447 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166677, d167447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166677, d167447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15062 (p : Pattern) (selected : d13059 p = 0) : d69112 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9943 q = 0) : d69108 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9943, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6695 q selected
    | true =>
      simp only [d9943, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9945 q = 0) : d69109 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9945, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9945, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13057 q = 0) : d69110 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13057, d69110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13057, d69110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13058 q = 0) : d69111 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13058, d69111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13058, d69111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13059 q = 0) : d69112 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13059, d69112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13059, d69112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro15063 (p : Pattern) (selected : d166683 p = 0) : d167391 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136105 q = 0) : d137360 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136105, d137360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136105, d137360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6159 q selected
  have h2 (q : Pattern) (selected : d136106 q = 0) : d137361 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136106, d137361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136106, d137361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166679 q = 0) : d167387 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166679, d167387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166679, d167387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15062 q selected
  have h4 (q : Pattern) (selected : d166680 q = 0) : d167388 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166680, d167388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166680, d167388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166681 q = 0) : d167389 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166681, d167389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166681, d167389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136107 q = 0) : d137362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136107, d137362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136107, d137362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6160 q selected
  have h7 (q : Pattern) (selected : d136108 q = 0) : d137363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136108, d137363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136108, d137363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136110 q = 0) : d137365 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136110, d137365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136110, d137365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d166682 q = 0) : d167390 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166682, d167390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166682, d167390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166683 q = 0) : d167391 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166683, d167391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166683, d167391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15064 (p : Pattern) (selected : d166689 p = 0) : d167397 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166684 q = 0) : d167392 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166684, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15063 q selected
    | true =>
      simp only [d166684, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166685 q = 0) : d167393 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166685, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166685, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136117 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136117, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11716 q selected
    | true =>
      simp only [d136117, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136118 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136118, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136118, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166686 q = 0) : d167394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166686, d167394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166686, d167394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166687 q = 0) : d167395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166687, d167395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166687, d167395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166688 q = 0) : d167396 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166688, d167396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166688, d167396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166689 q = 0) : d167397 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166689, d167397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166689, d167397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15065 (p : Pattern) (selected : d166695 p = 0) : d167453 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166622 q = 0) : d167392 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166622, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15050 q selected
    | true =>
      simp only [d166622, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166623 q = 0) : d167393 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166623, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166623, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166692 q = 0) : d167450 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166692, d167450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166692, d167450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166693 q = 0) : d167451 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166693, d167451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166693, d167451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d166694 q = 0) : d167452 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166694, d167452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166694, d167452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d166695 q = 0) : d167453 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166695, d167453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166695, d167453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15066 (p : Pattern) (selected : d166701 p = 0) : d167459 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166648 q = 0) : d167418 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166648, d167418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15055 q selected
    | true =>
      simp only [d166648, d167418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11710 q selected
  have h2 (q : Pattern) (selected : d166649 q = 0) : d167419 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166649, d167419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166649, d167419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166650 q = 0) : d167420 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166650, d167420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166650, d167420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166651 q = 0) : d167421 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166651, d167421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166651, d167421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166655 q = 0) : d167425 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166655, d167425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15056 q selected
    | true =>
      simp only [d166655, d167425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11712 q selected
  have h6 (q : Pattern) (selected : d166656 q = 0) : d167426 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166656, d167426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166656, d167426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166657 q = 0) : d167427 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166657, d167427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166657, d167427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166678 q = 0) : d167448 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166678, d167448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15060 q selected
    | true =>
      simp only [d166678, d167448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15061 q selected
  have h9 (q : Pattern) (selected : d166690 q = 0) : d167398 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166690, d167398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15064 q selected
    | true =>
      simp only [d166690, d167398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11718 q selected
  have h10 (q : Pattern) (selected : d166691 q = 0) : d167449 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166691, d167449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d166691, d167449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166696 q = 0) : d167454 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166696, d167454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15065 q selected
    | true =>
      simp only [d166696, d167454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d166697 q = 0) : d167455 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166697, d167455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166697, d167455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d166698 q = 0) : d167456 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166698, d167456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166698, d167456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d166699 q = 0) : d167457 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166699, d167457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166699, d167457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d166700 q = 0) : d167458 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166700, d167458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166700, d167458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d166701 q = 0) : d167459 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166701, d167459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166701, d167459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro15067 (p : Pattern) (selected : d166702 p = 0) : d167460 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166622 q = 0) : d167392 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166622, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15050 q selected
    | true =>
      simp only [d166622, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166623 q = 0) : d167393 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166623, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166623, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166624 q = 0) : d167394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166624, d167394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166624, d167394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166625 q = 0) : d167395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166625, d167395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166625, d167395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166646 q = 0) : d167416 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166646, d167416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166646, d167416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166702 q = 0) : d167460 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166702, d167460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166702, d167460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15068 (p : Pattern) (selected : d166707 p = 0) : d167465 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166622 q = 0) : d167392 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166622, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15050 q selected
    | true =>
      simp only [d166622, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166623 q = 0) : d167393 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166623, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166623, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166624 q = 0) : d167394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166624, d167394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166624, d167394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166652 q = 0) : d167422 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166652, d167422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166652, d167422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166653 q = 0) : d167423 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166653, d167423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166653, d167423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166707 q = 0) : d167465 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166707, d167465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166707, d167465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15069 (p : Pattern) (selected : d166711 p = 0) : d167469 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166663 q = 0) : d167433 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166663, d167433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15058 q selected
    | true =>
      simp only [d166663, d167433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166664 q = 0) : d167434 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166664, d167434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166664, d167434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166668 q = 0) : d167438 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166668, d167438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15059 q selected
    | true =>
      simp only [d166668, d167438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166669 q = 0) : d167439 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166669, d167439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166669, d167439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166670 q = 0) : d167440 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166670, d167440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166670, d167440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166671 q = 0) : d167441 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166671, d167441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166671, d167441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166672 q = 0) : d167442 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166672, d167442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166672, d167442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166711 q = 0) : d167469 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166711, d167469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166711, d167469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15070 (p : Pattern) (selected : d166712 p = 0) : d167470 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166668 q = 0) : d167438 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166668, d167438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15059 q selected
    | true =>
      simp only [d166668, d167438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166669 q = 0) : d167439 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166669, d167439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166669, d167439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166674 q = 0) : d167444 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166674, d167444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166674, d167444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166675 q = 0) : d167445 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166675, d167445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166675, d167445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166676 q = 0) : d167446 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166676, d167446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166676, d167446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166712 q = 0) : d167470 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166712, d167470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166712, d167470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15071 (p : Pattern) (selected : d166714 p = 0) : d167406 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166684 q = 0) : d167392 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166684, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15063 q selected
    | true =>
      simp only [d166684, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166685 q = 0) : d167393 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166685, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166685, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136117 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136117, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11716 q selected
    | true =>
      simp only [d136117, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136118 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136118, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136118, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166686 q = 0) : d167394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166686, d167394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166686, d167394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166687 q = 0) : d167395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166687, d167395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166687, d167395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166688 q = 0) : d167396 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166688, d167396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166688, d167396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166714 q = 0) : d167406 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166714, d167406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166714, d167406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15072 (p : Pattern) (selected : d166717 p = 0) : d167473 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166622 q = 0) : d167392 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166622, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15050 q selected
    | true =>
      simp only [d166622, d167392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166623 q = 0) : d167393 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166623, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166623, d167393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166692 q = 0) : d167450 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166692, d167450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166692, d167450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166693 q = 0) : d167451 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166693, d167451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166693, d167451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d166694 q = 0) : d167452 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166694, d167452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166694, d167452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d166717 q = 0) : d167473 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166717, d167473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166717, d167473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15073 (p : Pattern) (selected : d166723 p = 0) : d167479 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166648 q = 0) : d167418 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166648, d167418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15055 q selected
    | true =>
      simp only [d166648, d167418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11710 q selected
  have h2 (q : Pattern) (selected : d166649 q = 0) : d167419 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166649, d167419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166649, d167419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166650 q = 0) : d167420 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166650, d167420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166650, d167420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166651 q = 0) : d167421 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166651, d167421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166651, d167421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166655 q = 0) : d167425 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166655, d167425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15056 q selected
    | true =>
      simp only [d166655, d167425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11712 q selected
  have h6 (q : Pattern) (selected : d166656 q = 0) : d167426 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166656, d167426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166656, d167426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166657 q = 0) : d167427 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166657, d167427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166657, d167427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166678 q = 0) : d167448 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166678, d167448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15060 q selected
    | true =>
      simp only [d166678, d167448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15061 q selected
  have h9 (q : Pattern) (selected : d166690 q = 0) : d167398 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166690, d167398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15064 q selected
    | true =>
      simp only [d166690, d167398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11718 q selected
  have h10 (q : Pattern) (selected : d166691 q = 0) : d167449 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166691, d167449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d166691, d167449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166696 q = 0) : d167454 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166696, d167454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15065 q selected
    | true =>
      simp only [d166696, d167454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d166697 q = 0) : d167455 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166697, d167455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166697, d167455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d166698 q = 0) : d167456 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166698, d167456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166698, d167456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d166699 q = 0) : d167457 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166699, d167457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166699, d167457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d166700 q = 0) : d167458 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166700, d167458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166700, d167458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d166703 q = 0) : d167461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166703, d167461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15067 q selected
    | true =>
      simp only [d166703, d167461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11724 q selected
  have h17 (q : Pattern) (selected : d166704 q = 0) : d167462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166704, d167462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166704, d167462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d166705 q = 0) : d167463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166705, d167463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d166705, d167463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d166706 q = 0) : d167464 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166706, d167464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166706, d167464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d166708 q = 0) : d167466 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166708, d167466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15068 q selected
    | true =>
      simp only [d166708, d167466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11726 q selected
  have h21 (q : Pattern) (selected : d166709 q = 0) : d167467 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166709, d167467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166709, d167467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d166710 q = 0) : d167468 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166710, d167468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d166710, d167468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d166713 q = 0) : d167471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166713, d167471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15069 q selected
    | true =>
      simp only [d166713, d167471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15070 q selected
  have h24 (q : Pattern) (selected : d166715 q = 0) : d167407 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166715, d167407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15071 q selected
    | true =>
      simp only [d166715, d167407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11729 q selected
  have h25 (q : Pattern) (selected : d166716 q = 0) : d167472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166716, d167472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d166716, d167472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d166718 q = 0) : d167474 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166718, d167474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15072 q selected
    | true =>
      simp only [d166718, d167474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d166719 q = 0) : d167475 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166719, d167475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d166719, d167475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d166720 q = 0) : d167476 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166720, d167476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d166720, d167476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d166721 q = 0) : d167477 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166721, d167477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d166721, d167477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d166722 q = 0) : d167478 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166722, d167478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d166722, d167478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d166723 q = 0) : d167479 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166723, d167479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d166723, d167479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro15074 (p : Pattern) (selected : d166730 p = 0) : d167486 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166725 q = 0) : d167481 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166725, d167481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15061 q selected
    | true =>
      simp only [d166725, d167481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11704 q selected
  have h2 (q : Pattern) (selected : d166726 q = 0) : d167482 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166726, d167482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166726, d167482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166727 q = 0) : d167483 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166727, d167483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166727, d167483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166728 q = 0) : d167484 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166728, d167484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166728, d167484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166729 q = 0) : d167485 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166729, d167485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166729, d167485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136171 q = 0) : d137470 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136171, d137470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11704 q selected
    | true =>
      simp only [d136171, d137470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136172 q = 0) : d137471 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136172, d137471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136172, d137471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136173 q = 0) : d137472 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136173, d137472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136173, d137472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d136174 q = 0) : d137473 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136174, d137473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136174, d137473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136175 q = 0) : d137474 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136175, d137474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136175, d137474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166730 q = 0) : d167486 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166730, d167486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166730, d167486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15075 (p : Pattern) (selected : d166737 p = 0) : d167493 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166713 q = 0) : d167471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166713, d167471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15069 q selected
    | true =>
      simp only [d166713, d167471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15070 q selected
  have h2 (q : Pattern) (selected : d166715 q = 0) : d167407 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166715, d167407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15071 q selected
    | true =>
      simp only [d166715, d167407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11729 q selected
  have h3 (q : Pattern) (selected : d166716 q = 0) : d167472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166716, d167472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166716, d167472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166718 q = 0) : d167474 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166718, d167474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15072 q selected
    | true =>
      simp only [d166718, d167474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d166719 q = 0) : d167475 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166719, d167475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166719, d167475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d166720 q = 0) : d167476 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166720, d167476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166720, d167476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166735 q = 0) : d167491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166735, d167491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166735, d167491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166736 q = 0) : d167492 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166736, d167492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166736, d167492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d166737 q = 0) : d167493 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166737, d167493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166737, d167493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15076 (p : Pattern) (selected : d6354 p = 0) : d76094 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d6350 q = 0) : d76090 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6350, d76090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6350, d76090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2799 q selected
  have h2 (q : Pattern) (selected : d5018 q = 0) : d69108 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2799 q selected
    | true =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6351 q = 0) : d76091 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6351, d76091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6351, d76091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5019 q = 0) : d69109 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6352 q = 0) : d76092 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6352, d76092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6352, d76092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6353 q = 0) : d76093 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6353, d76093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6353, d76093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d6354 q = 0) : d76094 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6354, d76094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6354, d76094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro15077 (p : Pattern) (selected : d13168 p = 0) : d113460 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13160 q = 0) : d113452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13160, d113452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13160, d113452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6677 q selected
  have h2 (q : Pattern) (selected : d9814 q = 0) : d101335 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6677 q selected
    | true =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13161 q = 0) : d113453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13161, d113453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13161, d113453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9816 q = 0) : d101337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, d101337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9816, d101337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13162 q = 0) : d113454 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13162, d113454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13162, d113454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13163 q = 0) : d113455 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13163, d113455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13163, d113455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13164 q = 0) : d113456 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13164, d113456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13164, d113456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8289 q selected
  have h8 (q : Pattern) (selected : d13025 q = 0) : d113355 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8289 q selected
    | true =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13165 q = 0) : d113457 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13165, d113457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13165, d113457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13026 q = 0) : d113356 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d13166 q = 0) : d113458 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13166, d113458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13166, d113458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d13167 q = 0) : d113459 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13167, d113459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d13167, d113459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d13168 q = 0) : d113460 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13168, d113460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13168, d113460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro15078 (p : Pattern) (selected : d166750 p = 0) : d167506 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136197 q = 0) : d137496 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136197, d137496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136197, d137496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6182 q selected
  have h2 (q : Pattern) (selected : d136198 q = 0) : d137497 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136198, d137497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136198, d137497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166743 q = 0) : d167499 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166743, d167499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166743, d167499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15077 q selected
  have h4 (q : Pattern) (selected : d166744 q = 0) : d167500 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166744, d167500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166744, d167500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166745 q = 0) : d167501 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166745, d167501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166745, d167501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136199 q = 0) : d137498 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136199, d137498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136199, d137498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6183 q selected
  have h7 (q : Pattern) (selected : d136200 q = 0) : d137499 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136200, d137499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136200, d137499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166746 q = 0) : d167502 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166746, d167502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166746, d167502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15076 q selected
  have h9 (q : Pattern) (selected : d166747 q = 0) : d167503 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166747, d167503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166747, d167503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166748 q = 0) : d167504 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166748, d167504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166748, d167504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166749 q = 0) : d167505 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166749, d167505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166749, d167505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d166750 q = 0) : d167506 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166750, d167506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166750, d167506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro15079 (p : Pattern) (selected : d166755 p = 0) : d167511 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136199 q = 0) : d137498 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136199, d137498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136199, d137498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6183 q selected
  have h2 (q : Pattern) (selected : d136200 q = 0) : d137499 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136200, d137499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136200, d137499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166746 q = 0) : d167502 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166746, d167502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166746, d167502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15076 q selected
  have h4 (q : Pattern) (selected : d166747 q = 0) : d167503 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166747, d167503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166747, d167503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166748 q = 0) : d167504 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166748, d167504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166748, d167504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166753 q = 0) : d167509 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166753, d167509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166753, d167509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166754 q = 0) : d167510 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166754, d167510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166754, d167510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166755 q = 0) : d167511 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166755, d167511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166755, d167511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15080 (p : Pattern) (selected : d166761 p = 0) : d167517 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166751 q = 0) : d167507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166751, d167507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15078 q selected
    | true =>
      simp only [d166751, d167507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166752 q = 0) : d167508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166752, d167508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166752, d167508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166756 q = 0) : d167512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166756, d167512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15079 q selected
    | true =>
      simp only [d166756, d167512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166757 q = 0) : d167513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166757, d167513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166757, d167513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166758 q = 0) : d167514 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166758, d167514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166758, d167514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166759 q = 0) : d167515 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166759, d167515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166759, d167515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166760 q = 0) : d167516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166760, d167516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166760, d167516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166761 q = 0) : d167517 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166761, d167517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166761, d167517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15081 (p : Pattern) (selected : d166765 p = 0) : d167521 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166756 q = 0) : d167512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166756, d167512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15079 q selected
    | true =>
      simp only [d166756, d167512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166757 q = 0) : d167513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166757, d167513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166757, d167513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136220 q = 0) : d137519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136220, d137519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11739 q selected
    | true =>
      simp only [d136220, d137519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136221 q = 0) : d137520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136221, d137520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136221, d137520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166762 q = 0) : d167518 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166762, d167518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166762, d167518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166763 q = 0) : d167519 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166763, d167519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166763, d167519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166764 q = 0) : d167520 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166764, d167520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166764, d167520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166765 q = 0) : d167521 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166765, d167521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166765, d167521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15082 (p : Pattern) (selected : d13213 p = 0) : d76094 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13209 q = 0) : d76090 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13209, d76090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13209, d76090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6695 q selected
  have h2 (q : Pattern) (selected : d9943 q = 0) : d69108 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9943, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6695 q selected
    | true =>
      simp only [d9943, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13210 q = 0) : d76091 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13210, d76091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13210, d76091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9945 q = 0) : d69109 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9945, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9945, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13211 q = 0) : d76092 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13211, d76092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13211, d76092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13212 q = 0) : d76093 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13212, d76093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13212, d76093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13213 q = 0) : d76094 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13213, d76094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13213, d76094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro15083 (p : Pattern) (selected : d166771 p = 0) : d167524 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136227 q = 0) : d137498 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136227, d137498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136227, d137498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6191 q selected
  have h2 (q : Pattern) (selected : d136228 q = 0) : d137499 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136228, d137499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136228, d137499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166767 q = 0) : d167502 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166767, d167502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166767, d167502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15082 q selected
  have h4 (q : Pattern) (selected : d166768 q = 0) : d167503 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166768, d167503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166768, d167503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166769 q = 0) : d167504 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166769, d167504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166769, d167504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136229 q = 0) : d137501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136229, d137501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136229, d137501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6192 q selected
  have h7 (q : Pattern) (selected : d136230 q = 0) : d137502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136230, d137502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136230, d137502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136232 q = 0) : d137508 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136232, d137508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136232, d137508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d166770 q = 0) : d167523 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166770, d167523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166770, d167523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166771 q = 0) : d167524 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166771, d167524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166771, d167524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15084 (p : Pattern) (selected : d166777 p = 0) : d167530 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166772 q = 0) : d167525 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166772, d167525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15083 q selected
    | true =>
      simp only [d166772, d167525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166773 q = 0) : d167526 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166773, d167526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166773, d167526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136239 q = 0) : d137519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136239, d137519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11742 q selected
    | true =>
      simp only [d136239, d137519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136240 q = 0) : d137520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136240, d137520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136240, d137520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166774 q = 0) : d167527 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166774, d167527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166774, d167527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166775 q = 0) : d167528 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166775, d167528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166775, d167528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166776 q = 0) : d167529 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166776, d167529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166776, d167529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166777 q = 0) : d167530 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166777, d167530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166777, d167530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15085 (p : Pattern) (selected : d166781 p = 0) : d167524 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136199 q = 0) : d137498 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136199, d137498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136199, d137498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6183 q selected
  have h2 (q : Pattern) (selected : d136200 q = 0) : d137499 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136200, d137499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136200, d137499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166746 q = 0) : d167502 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166746, d167502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166746, d167502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15076 q selected
  have h4 (q : Pattern) (selected : d166747 q = 0) : d167503 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166747, d167503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166747, d167503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166748 q = 0) : d167504 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166748, d167504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166748, d167504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136202 q = 0) : d137501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136202, d137501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136202, d137501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6184 q selected
  have h7 (q : Pattern) (selected : d136203 q = 0) : d137502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136203, d137502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136203, d137502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136209 q = 0) : d137508 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136209, d137508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136209, d137508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d166780 q = 0) : d167523 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166780, d167523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166780, d167523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166781 q = 0) : d167524 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166781, d167524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166781, d167524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15086 (p : Pattern) (selected : d166787 p = 0) : d167536 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166782 q = 0) : d167525 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166782, d167525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15085 q selected
    | true =>
      simp only [d166782, d167525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166783 q = 0) : d167526 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166783, d167526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166783, d167526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166784 q = 0) : d167533 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166784, d167533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166784, d167533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166785 q = 0) : d167534 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166785, d167534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166785, d167534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d166786 q = 0) : d167535 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166786, d167535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166786, d167535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d166787 q = 0) : d167536 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166787, d167536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166787, d167536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15087 (p : Pattern) (selected : d166793 p = 0) : d167542 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166766 q = 0) : d167522 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166766, d167522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15080 q selected
    | true =>
      simp only [d166766, d167522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15081 q selected
  have h2 (q : Pattern) (selected : d166778 q = 0) : d167531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166778, d167531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15084 q selected
    | true =>
      simp only [d166778, d167531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11744 q selected
  have h3 (q : Pattern) (selected : d166779 q = 0) : d167532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166779, d167532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166779, d167532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166788 q = 0) : d167537 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166788, d167537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15086 q selected
    | true =>
      simp only [d166788, d167537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d166789 q = 0) : d167538 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166789, d167538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166789, d167538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d166790 q = 0) : d167539 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166790, d167539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166790, d167539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166791 q = 0) : d167540 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166791, d167540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166791, d167540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166792 q = 0) : d167541 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166792, d167541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166792, d167541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d166793 q = 0) : d167542 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166793, d167542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166793, d167542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15088 (p : Pattern) (selected : d166799 p = 0) : d167548 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166634 q = 0) : d167404 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166634, d167404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166634, d167404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15052 q selected
  have h2 (q : Pattern) (selected : d166635 q = 0) : d167405 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166635, d167405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166635, d167405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d166643 q = 0) : d167413 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166643, d167413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15052 q selected
    | true =>
      simp only [d166643, d167413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15054 q selected
  have h4 (q : Pattern) (selected : d166644 q = 0) : d167414 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166644, d167414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166644, d167414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d166645 q = 0) : d167415 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166645, d167415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166645, d167415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166724 q = 0) : d167480 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166724, d167480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15066 q selected
    | true =>
      simp only [d166724, d167480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15073 q selected
  have h7 (q : Pattern) (selected : d166731 q = 0) : d167487 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166731, d167487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15074 q selected
    | true =>
      simp only [d166731, d167487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11733 q selected
  have h8 (q : Pattern) (selected : d166732 q = 0) : d167488 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166732, d167488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166732, d167488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d166733 q = 0) : d167489 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166733, d167489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d166733, d167489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d166734 q = 0) : d167490 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166734, d167490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166734, d167490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166738 q = 0) : d167494 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166738, d167494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166738, d167494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15075 q selected
  have h12 (q : Pattern) (selected : d136192 q = 0) : d137491 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136192, d137491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136192, d137491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11735 q selected
  have h13 (q : Pattern) (selected : d166739 q = 0) : d167495 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166739, d167495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166739, d167495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d166740 q = 0) : d167496 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166740, d167496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d166740, d167496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d166741 q = 0) : d167497 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166741, d167497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d166741, d167497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d166742 q = 0) : d167498 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d166742, d167498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166742, d167498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d166794 q = 0) : d167543 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166794, d167543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166794, d167543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15087 q selected
  have h18 (q : Pattern) (selected : d136279 q = 0) : d137556 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136279, d137556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136279, d137556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11750 q selected
  have h19 (q : Pattern) (selected : d166795 q = 0) : d167544 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166795, d167544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d166795, d167544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d166796 q = 0) : d167545 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166796, d167545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d166796, d167545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d166797 q = 0) : d167546 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166797, d167546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d166797, d167546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d166798 q = 0) : d167547 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d166798, d167547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d166798, d167547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d166799 q = 0) : d167548 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d166799, d167548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d166799, d167548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro15089 (p : Pattern) (selected : d166805 p = 0) : d167554 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166800 q = 0) : d167549 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d166800, d167549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166800, d167549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15088 q selected
  have h2 (q : Pattern) (selected : d166801 q = 0) : d167550 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d166801, d167550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166801, d167550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166802 q = 0) : d167551 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d166802, d167551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166802, d167551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166803 q = 0) : d167552 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d166803, d167552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166803, d167552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166804 q = 0) : d167553 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d166804, d167553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166804, d167553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166805 q = 0) : d167554 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d166805, d167554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166805, d167554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15090 (p : Pattern) (selected : d5138 p = 0) : d69225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5134 q = 0) : d69221 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2814 q selected
    | true =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d5135 q = 0) : d69222 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d5136 q = 0) : d69223 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5136, d69223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5136, d69223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5137 q = 0) : d69224 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5137, d69224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5137, d69224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d5138 q = 0) : d69225 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5138, d69225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d5138, d69225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro15091 (p : Pattern) (selected : d166813 p = 0) : d167562 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136294 q = 0) : d137571 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136294, d137571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136294, d137571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6205 q selected
  have h2 (q : Pattern) (selected : d136295 q = 0) : d137572 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136295, d137572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136295, d137572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166809 q = 0) : d167558 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166809, d167558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166809, d167558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15090 q selected
  have h4 (q : Pattern) (selected : d166810 q = 0) : d167559 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166810, d167559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166810, d167559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166811 q = 0) : d167560 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166811, d167560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166811, d167560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136296 q = 0) : d137573 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136296, d137573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136296, d137573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6206 q selected
  have h7 (q : Pattern) (selected : d136297 q = 0) : d137574 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136297, d137574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136297, d137574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136299 q = 0) : d137576 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136299, d137576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136299, d137576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d166812 q = 0) : d167561 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166812, d167561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166812, d167561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166813 q = 0) : d167562 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166813, d167562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166813, d167562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15092 (p : Pattern) (selected : d166819 p = 0) : d167568 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166814 q = 0) : d167563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166814, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15091 q selected
    | true =>
      simp only [d166814, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166815 q = 0) : d167564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166815, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166815, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166816 q = 0) : d167565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166816, d167565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166816, d167565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166817 q = 0) : d167566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166817, d167566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166817, d167566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166818 q = 0) : d167567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166818, d167567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166818, d167567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166819 q = 0) : d167568 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166819, d167568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166819, d167568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15093 (p : Pattern) (selected : d166825 p = 0) : d167574 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166820 q = 0) : d167569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166820, d167569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15092 q selected
    | true =>
      simp only [d166820, d167569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11756 q selected
  have h2 (q : Pattern) (selected : d166821 q = 0) : d167570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166821, d167570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166821, d167570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166822 q = 0) : d167571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166822, d167571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166822, d167571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166823 q = 0) : d167572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166823, d167572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166823, d167572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166824 q = 0) : d167573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166824, d167573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166824, d167573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166825 q = 0) : d167574 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166825, d167574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166825, d167574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15094 (p : Pattern) (selected : d166828 p = 0) : d167577 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166814 q = 0) : d167563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166814, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15091 q selected
    | true =>
      simp only [d166814, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166815 q = 0) : d167564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166815, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166815, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166816 q = 0) : d167565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166816, d167565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166816, d167565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166817 q = 0) : d167566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166817, d167566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166817, d167566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166818 q = 0) : d167567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166818, d167567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166818, d167567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166828 q = 0) : d167577 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166828, d167577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166828, d167577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15095 (p : Pattern) (selected : d166834 p = 0) : d167583 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166820 q = 0) : d167569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166820, d167569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15092 q selected
    | true =>
      simp only [d166820, d167569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11756 q selected
  have h2 (q : Pattern) (selected : d166821 q = 0) : d167570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166821, d167570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166821, d167570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166822 q = 0) : d167571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166822, d167571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166822, d167571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166823 q = 0) : d167572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166823, d167572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166823, d167572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166824 q = 0) : d167573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166824, d167573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166824, d167573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166829 q = 0) : d167578 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166829, d167578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15094 q selected
    | true =>
      simp only [d166829, d167578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11759 q selected
  have h7 (q : Pattern) (selected : d166830 q = 0) : d167579 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166830, d167579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166830, d167579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166831 q = 0) : d167580 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166831, d167580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166831, d167580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d166832 q = 0) : d167581 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166832, d167581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166832, d167581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166833 q = 0) : d167582 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166833, d167582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166833, d167582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166834 q = 0) : d167583 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166834, d167583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166834, d167583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15096 (p : Pattern) (selected : d166839 p = 0) : d167588 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166814 q = 0) : d167563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166814, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15091 q selected
    | true =>
      simp only [d166814, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166815 q = 0) : d167564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166815, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166815, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166816 q = 0) : d167565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166816, d167565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166816, d167565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166817 q = 0) : d167566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166817, d167566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166817, d167566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166838 q = 0) : d167587 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166838, d167587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166838, d167587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166839 q = 0) : d167588 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166839, d167588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166839, d167588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15097 (p : Pattern) (selected : d166846 p = 0) : d167595 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166814 q = 0) : d167563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166814, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15091 q selected
    | true =>
      simp only [d166814, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166815 q = 0) : d167564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166815, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166815, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166816 q = 0) : d167565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166816, d167565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166816, d167565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166844 q = 0) : d167593 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166844, d167593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166844, d167593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166845 q = 0) : d167594 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166845, d167594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166845, d167594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166846 q = 0) : d167595 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166846, d167595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166846, d167595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15098 (p : Pattern) (selected : d13355 p = 0) : d113615 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10099 q = 0) : d101526 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6719 q selected
    | true =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10101 q = 0) : d101528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13348 q = 0) : d113608 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13348, d113608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13348, d113608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13349 q = 0) : d113609 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13349, d113609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13349, d113609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13351 q = 0) : d113611 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8358 q selected
    | true =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13352 q = 0) : d113612 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13353 q = 0) : d113613 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13353, d113613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13353, d113613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13354 q = 0) : d113614 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13354, d113614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13354, d113614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13355 q = 0) : d113615 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13355, d113615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13355, d113615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15099 (p : Pattern) (selected : d166854 p = 0) : d167603 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136352 q = 0) : d137629 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136352, d137629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136352, d137629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6220 q selected
  have h2 (q : Pattern) (selected : d136353 q = 0) : d137630 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136353, d137630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136353, d137630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166850 q = 0) : d167599 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166850, d167599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166850, d167599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15098 q selected
  have h4 (q : Pattern) (selected : d166851 q = 0) : d167600 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166851, d167600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166851, d167600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166852 q = 0) : d167601 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166852, d167601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166852, d167601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136294 q = 0) : d137571 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136294, d137571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136294, d137571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6205 q selected
  have h7 (q : Pattern) (selected : d136295 q = 0) : d137572 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136295, d137572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136295, d137572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166809 q = 0) : d167558 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166809, d167558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166809, d167558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15090 q selected
  have h9 (q : Pattern) (selected : d166810 q = 0) : d167559 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166810, d167559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166810, d167559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166811 q = 0) : d167560 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166811, d167560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166811, d167560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166853 q = 0) : d167602 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166853, d167602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166853, d167602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d166854 q = 0) : d167603 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166854, d167603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166854, d167603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro15100 (p : Pattern) (selected : d166859 p = 0) : d167608 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136294 q = 0) : d137571 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136294, d137571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136294, d137571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6205 q selected
  have h2 (q : Pattern) (selected : d136295 q = 0) : d137572 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136295, d137572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136295, d137572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166809 q = 0) : d167558 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166809, d167558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166809, d167558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15090 q selected
  have h4 (q : Pattern) (selected : d166810 q = 0) : d167559 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166810, d167559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166810, d167559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166811 q = 0) : d167560 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166811, d167560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166811, d167560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166857 q = 0) : d167606 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166857, d167606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166857, d167606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166858 q = 0) : d167607 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166858, d167607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166858, d167607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166859 q = 0) : d167608 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166859, d167608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166859, d167608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15101 (p : Pattern) (selected : d166865 p = 0) : d167614 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166855 q = 0) : d167604 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166855, d167604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15099 q selected
    | true =>
      simp only [d166855, d167604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166856 q = 0) : d167605 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166856, d167605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166856, d167605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166860 q = 0) : d167609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166860, d167609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15100 q selected
    | true =>
      simp only [d166860, d167609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166861 q = 0) : d167610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166861, d167610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166861, d167610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166862 q = 0) : d167611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166862, d167611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166862, d167611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166863 q = 0) : d167612 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166863, d167612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166863, d167612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166864 q = 0) : d167613 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166864, d167613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166864, d167613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166865 q = 0) : d167614 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166865, d167614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166865, d167614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15102 (p : Pattern) (selected : d166869 p = 0) : d167618 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166860 q = 0) : d167609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166860, d167609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15100 q selected
    | true =>
      simp only [d166860, d167609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166861 q = 0) : d167610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166861, d167610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166861, d167610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166866 q = 0) : d167615 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166866, d167615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166866, d167615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166867 q = 0) : d167616 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166867, d167616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166867, d167616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166868 q = 0) : d167617 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166868, d167617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166868, d167617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166869 q = 0) : d167618 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166869, d167618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166869, d167618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15103 (p : Pattern) (selected : d13385 p = 0) : d69225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10243 q = 0) : d69221 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10243, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6739 q selected
    | true =>
      simp only [d10243, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10245 q = 0) : d69222 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10245, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10245, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13383 q = 0) : d69223 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13383, d69223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13383, d69223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13384 q = 0) : d69224 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13384, d69224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13384, d69224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13385 q = 0) : d69225 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13385, d69225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13385, d69225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro15104 (p : Pattern) (selected : d166875 p = 0) : d167562 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136364 q = 0) : d137571 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136364, d137571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136364, d137571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6225 q selected
  have h2 (q : Pattern) (selected : d136365 q = 0) : d137572 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136365, d137572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136365, d137572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166871 q = 0) : d167558 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166871, d167558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166871, d167558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15103 q selected
  have h4 (q : Pattern) (selected : d166872 q = 0) : d167559 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166872, d167559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166872, d167559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166873 q = 0) : d167560 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166873, d167560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166873, d167560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136366 q = 0) : d137573 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136366, d137573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136366, d137573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6226 q selected
  have h7 (q : Pattern) (selected : d136367 q = 0) : d137574 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136367, d137574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136367, d137574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136369 q = 0) : d137576 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136369, d137576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136369, d137576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d166874 q = 0) : d167561 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166874, d167561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166874, d167561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166875 q = 0) : d167562 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166875, d167562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166875, d167562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15105 (p : Pattern) (selected : d166881 p = 0) : d167568 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166876 q = 0) : d167563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166876, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15104 q selected
    | true =>
      simp only [d166876, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166877 q = 0) : d167564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166877, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166877, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136376 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136376, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11768 q selected
    | true =>
      simp only [d136376, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136377 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136377, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136377, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166878 q = 0) : d167565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166878, d167565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166878, d167565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166879 q = 0) : d167566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166879, d167566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166879, d167566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166880 q = 0) : d167567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166880, d167567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166880, d167567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166881 q = 0) : d167568 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166881, d167568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166881, d167568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15106 (p : Pattern) (selected : d166887 p = 0) : d167624 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166814 q = 0) : d167563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166814, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15091 q selected
    | true =>
      simp only [d166814, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166815 q = 0) : d167564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166815, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166815, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166884 q = 0) : d167621 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166884, d167621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166884, d167621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166885 q = 0) : d167622 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166885, d167622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166885, d167622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d166886 q = 0) : d167623 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166886, d167623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166886, d167623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d166887 q = 0) : d167624 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166887, d167624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166887, d167624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15107 (p : Pattern) (selected : d166893 p = 0) : d167630 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166840 q = 0) : d167589 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166840, d167589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15096 q selected
    | true =>
      simp only [d166840, d167589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11762 q selected
  have h2 (q : Pattern) (selected : d166841 q = 0) : d167590 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166841, d167590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166841, d167590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166842 q = 0) : d167591 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166842, d167591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166842, d167591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166843 q = 0) : d167592 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166843, d167592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166843, d167592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166847 q = 0) : d167596 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166847, d167596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15097 q selected
    | true =>
      simp only [d166847, d167596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11764 q selected
  have h6 (q : Pattern) (selected : d166848 q = 0) : d167597 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166848, d167597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166848, d167597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166849 q = 0) : d167598 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166849, d167598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166849, d167598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166870 q = 0) : d167619 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166870, d167619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15101 q selected
    | true =>
      simp only [d166870, d167619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15102 q selected
  have h9 (q : Pattern) (selected : d166882 q = 0) : d167569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166882, d167569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15105 q selected
    | true =>
      simp only [d166882, d167569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11770 q selected
  have h10 (q : Pattern) (selected : d166883 q = 0) : d167620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166883, d167620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d166883, d167620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166888 q = 0) : d167625 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166888, d167625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15106 q selected
    | true =>
      simp only [d166888, d167625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d166889 q = 0) : d167626 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166889, d167626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166889, d167626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d166890 q = 0) : d167627 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166890, d167627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166890, d167627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d166891 q = 0) : d167628 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166891, d167628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166891, d167628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d166892 q = 0) : d167629 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166892, d167629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166892, d167629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d166893 q = 0) : d167630 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166893, d167630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166893, d167630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro15108 (p : Pattern) (selected : d166894 p = 0) : d167631 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166814 q = 0) : d167563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166814, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15091 q selected
    | true =>
      simp only [d166814, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166815 q = 0) : d167564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166815, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166815, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166816 q = 0) : d167565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166816, d167565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166816, d167565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166817 q = 0) : d167566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166817, d167566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166817, d167566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166838 q = 0) : d167587 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166838, d167587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166838, d167587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166894 q = 0) : d167631 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166894, d167631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166894, d167631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15109 (p : Pattern) (selected : d166899 p = 0) : d167636 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166814 q = 0) : d167563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166814, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15091 q selected
    | true =>
      simp only [d166814, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166815 q = 0) : d167564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166815, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166815, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166816 q = 0) : d167565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166816, d167565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166816, d167565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166844 q = 0) : d167593 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166844, d167593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166844, d167593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166845 q = 0) : d167594 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166845, d167594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166845, d167594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166899 q = 0) : d167636 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166899, d167636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166899, d167636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15110 (p : Pattern) (selected : d166903 p = 0) : d167640 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166855 q = 0) : d167604 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166855, d167604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15099 q selected
    | true =>
      simp only [d166855, d167604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166856 q = 0) : d167605 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166856, d167605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166856, d167605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166860 q = 0) : d167609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166860, d167609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15100 q selected
    | true =>
      simp only [d166860, d167609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166861 q = 0) : d167610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166861, d167610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166861, d167610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166862 q = 0) : d167611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166862, d167611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166862, d167611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166863 q = 0) : d167612 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166863, d167612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166863, d167612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166864 q = 0) : d167613 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166864, d167613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166864, d167613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166903 q = 0) : d167640 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166903, d167640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166903, d167640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15111 (p : Pattern) (selected : d166904 p = 0) : d167641 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166860 q = 0) : d167609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166860, d167609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15100 q selected
    | true =>
      simp only [d166860, d167609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166861 q = 0) : d167610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166861, d167610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166861, d167610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166866 q = 0) : d167615 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166866, d167615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166866, d167615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166867 q = 0) : d167616 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166867, d167616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166867, d167616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166868 q = 0) : d167617 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166868, d167617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166868, d167617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166904 q = 0) : d167641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166904, d167641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166904, d167641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15112 (p : Pattern) (selected : d166906 p = 0) : d167577 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166876 q = 0) : d167563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166876, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15104 q selected
    | true =>
      simp only [d166876, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166877 q = 0) : d167564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166877, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166877, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136376 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136376, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11768 q selected
    | true =>
      simp only [d136376, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136377 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136377, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136377, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166878 q = 0) : d167565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166878, d167565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166878, d167565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166879 q = 0) : d167566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166879, d167566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166879, d167566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166880 q = 0) : d167567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166880, d167567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166880, d167567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166906 q = 0) : d167577 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166906, d167577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166906, d167577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15113 (p : Pattern) (selected : d166909 p = 0) : d167644 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166814 q = 0) : d167563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166814, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15091 q selected
    | true =>
      simp only [d166814, d167563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166815 q = 0) : d167564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166815, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166815, d167564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166884 q = 0) : d167621 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166884, d167621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166884, d167621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166885 q = 0) : d167622 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166885, d167622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166885, d167622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d166886 q = 0) : d167623 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166886, d167623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166886, d167623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d166909 q = 0) : d167644 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166909, d167644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166909, d167644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15114 (p : Pattern) (selected : d166915 p = 0) : d167650 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166840 q = 0) : d167589 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166840, d167589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15096 q selected
    | true =>
      simp only [d166840, d167589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11762 q selected
  have h2 (q : Pattern) (selected : d166841 q = 0) : d167590 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166841, d167590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166841, d167590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166842 q = 0) : d167591 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166842, d167591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166842, d167591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166843 q = 0) : d167592 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166843, d167592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166843, d167592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166847 q = 0) : d167596 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166847, d167596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15097 q selected
    | true =>
      simp only [d166847, d167596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11764 q selected
  have h6 (q : Pattern) (selected : d166848 q = 0) : d167597 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166848, d167597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166848, d167597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166849 q = 0) : d167598 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166849, d167598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166849, d167598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166870 q = 0) : d167619 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166870, d167619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15101 q selected
    | true =>
      simp only [d166870, d167619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15102 q selected
  have h9 (q : Pattern) (selected : d166882 q = 0) : d167569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166882, d167569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15105 q selected
    | true =>
      simp only [d166882, d167569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11770 q selected
  have h10 (q : Pattern) (selected : d166883 q = 0) : d167620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166883, d167620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d166883, d167620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166888 q = 0) : d167625 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166888, d167625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15106 q selected
    | true =>
      simp only [d166888, d167625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d166889 q = 0) : d167626 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166889, d167626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166889, d167626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d166890 q = 0) : d167627 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166890, d167627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166890, d167627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d166891 q = 0) : d167628 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166891, d167628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166891, d167628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d166892 q = 0) : d167629 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166892, d167629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166892, d167629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d166895 q = 0) : d167632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166895, d167632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15108 q selected
    | true =>
      simp only [d166895, d167632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11776 q selected
  have h17 (q : Pattern) (selected : d166896 q = 0) : d167633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166896, d167633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166896, d167633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d166897 q = 0) : d167634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166897, d167634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d166897, d167634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d166898 q = 0) : d167635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166898, d167635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166898, d167635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d166900 q = 0) : d167637 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166900, d167637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15109 q selected
    | true =>
      simp only [d166900, d167637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11778 q selected
  have h21 (q : Pattern) (selected : d166901 q = 0) : d167638 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166901, d167638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166901, d167638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d166902 q = 0) : d167639 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166902, d167639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d166902, d167639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d166905 q = 0) : d167642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166905, d167642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15110 q selected
    | true =>
      simp only [d166905, d167642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15111 q selected
  have h24 (q : Pattern) (selected : d166907 q = 0) : d167578 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166907, d167578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15112 q selected
    | true =>
      simp only [d166907, d167578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11781 q selected
  have h25 (q : Pattern) (selected : d166908 q = 0) : d167643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166908, d167643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d166908, d167643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d166910 q = 0) : d167645 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166910, d167645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15113 q selected
    | true =>
      simp only [d166910, d167645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d166911 q = 0) : d167646 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166911, d167646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d166911, d167646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d166912 q = 0) : d167647 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166912, d167647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d166912, d167647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d166913 q = 0) : d167648 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166913, d167648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d166913, d167648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d166914 q = 0) : d167649 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166914, d167649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d166914, d167649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d166915 q = 0) : d167650 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166915, d167650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d166915, d167650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro15115 (p : Pattern) (selected : d166922 p = 0) : d167657 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166917 q = 0) : d167652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166917, d167652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15102 q selected
    | true =>
      simp only [d166917, d167652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11756 q selected
  have h2 (q : Pattern) (selected : d166918 q = 0) : d167653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166918, d167653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166918, d167653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166919 q = 0) : d167654 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166919, d167654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166919, d167654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166920 q = 0) : d167655 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166920, d167655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166920, d167655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166921 q = 0) : d167656 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166921, d167656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166921, d167656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136430 q = 0) : d137681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136430, d137681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11756 q selected
    | true =>
      simp only [d136430, d137681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136431 q = 0) : d137682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136431, d137682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136431, d137682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136432 q = 0) : d137683 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136432, d137683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136432, d137683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d136433 q = 0) : d137684 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136433, d137684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136433, d137684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136434 q = 0) : d137685 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136434, d137685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136434, d137685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166922 q = 0) : d167657 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166922, d167657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166922, d167657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15116 (p : Pattern) (selected : d166929 p = 0) : d167664 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166905 q = 0) : d167642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166905, d167642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15110 q selected
    | true =>
      simp only [d166905, d167642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15111 q selected
  have h2 (q : Pattern) (selected : d166907 q = 0) : d167578 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166907, d167578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15112 q selected
    | true =>
      simp only [d166907, d167578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11781 q selected
  have h3 (q : Pattern) (selected : d166908 q = 0) : d167643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166908, d167643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166908, d167643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166910 q = 0) : d167645 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166910, d167645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15113 q selected
    | true =>
      simp only [d166910, d167645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d166911 q = 0) : d167646 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166911, d167646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166911, d167646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d166912 q = 0) : d167647 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166912, d167647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166912, d167647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166927 q = 0) : d167662 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166927, d167662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166927, d167662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166928 q = 0) : d167663 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166928, d167663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166928, d167663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d166929 q = 0) : d167664 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166929, d167664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166929, d167664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15117 (p : Pattern) (selected : d6500 p = 0) : d76229 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d6496 q = 0) : d76225 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6496, d76225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6496, d76225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2814 q selected
  have h2 (q : Pattern) (selected : d5134 q = 0) : d69221 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2814 q selected
    | true =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6497 q = 0) : d76226 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6497, d76226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6497, d76226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5135 q = 0) : d69222 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6498 q = 0) : d76227 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6498, d76227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6498, d76227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6499 q = 0) : d76228 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6499, d76228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6499, d76228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d6500 q = 0) : d76229 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6500, d76229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6500, d76229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro15118 (p : Pattern) (selected : d13494 p = 0) : d113716 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13486 q = 0) : d113708 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13486, d113708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13486, d113708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6719 q selected
  have h2 (q : Pattern) (selected : d10099 q = 0) : d101526 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6719 q selected
    | true =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13487 q = 0) : d113709 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13487, d113709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13487, d113709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10101 q = 0) : d101528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13488 q = 0) : d113710 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13488, d113710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13488, d113710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13489 q = 0) : d113711 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13489, d113711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13489, d113711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13490 q = 0) : d113712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13490, d113712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13490, d113712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8358 q selected
  have h8 (q : Pattern) (selected : d13351 q = 0) : d113611 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8358 q selected
    | true =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13491 q = 0) : d113713 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13491, d113713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13491, d113713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13352 q = 0) : d113612 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d13492 q = 0) : d113714 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13492, d113714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13492, d113714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d13493 q = 0) : d113715 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13493, d113715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d13493, d113715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d13494 q = 0) : d113716 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13494, d113716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13494, d113716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro15119 (p : Pattern) (selected : d166942 p = 0) : d167677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136456 q = 0) : d137707 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136456, d137707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136456, d137707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6248 q selected
  have h2 (q : Pattern) (selected : d136457 q = 0) : d137708 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136457, d137708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136457, d137708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166935 q = 0) : d167670 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166935, d167670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166935, d167670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15118 q selected
  have h4 (q : Pattern) (selected : d166936 q = 0) : d167671 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166936, d167671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166936, d167671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166937 q = 0) : d167672 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166937, d167672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166937, d167672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136458 q = 0) : d137709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136458, d137709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136458, d137709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6249 q selected
  have h7 (q : Pattern) (selected : d136459 q = 0) : d137710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136459, d137710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136459, d137710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166938 q = 0) : d167673 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166938, d167673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166938, d167673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15117 q selected
  have h9 (q : Pattern) (selected : d166939 q = 0) : d167674 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166939, d167674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166939, d167674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166940 q = 0) : d167675 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166940, d167675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166940, d167675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166941 q = 0) : d167676 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166941, d167676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166941, d167676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d166942 q = 0) : d167677 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166942, d167677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166942, d167677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro15120 (p : Pattern) (selected : d166947 p = 0) : d167682 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136458 q = 0) : d137709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136458, d137709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136458, d137709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6249 q selected
  have h2 (q : Pattern) (selected : d136459 q = 0) : d137710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136459, d137710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136459, d137710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166938 q = 0) : d167673 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166938, d167673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166938, d167673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15117 q selected
  have h4 (q : Pattern) (selected : d166939 q = 0) : d167674 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166939, d167674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166939, d167674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166940 q = 0) : d167675 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166940, d167675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166940, d167675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166945 q = 0) : d167680 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166945, d167680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166945, d167680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166946 q = 0) : d167681 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166946, d167681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166946, d167681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166947 q = 0) : d167682 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166947, d167682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166947, d167682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15121 (p : Pattern) (selected : d166953 p = 0) : d167688 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166943 q = 0) : d167678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166943, d167678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15119 q selected
    | true =>
      simp only [d166943, d167678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166944 q = 0) : d167679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166944, d167679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166944, d167679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166948 q = 0) : d167683 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166948, d167683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15120 q selected
    | true =>
      simp only [d166948, d167683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166949 q = 0) : d167684 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166949, d167684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166949, d167684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166950 q = 0) : d167685 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166950, d167685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166950, d167685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166951 q = 0) : d167686 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166951, d167686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166951, d167686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166952 q = 0) : d167687 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166952, d167687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166952, d167687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166953 q = 0) : d167688 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166953, d167688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166953, d167688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15122 (p : Pattern) (selected : d166957 p = 0) : d167692 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166948 q = 0) : d167683 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166948, d167683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15120 q selected
    | true =>
      simp only [d166948, d167683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166949 q = 0) : d167684 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166949, d167684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166949, d167684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136479 q = 0) : d137730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136479, d137730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11791 q selected
    | true =>
      simp only [d136479, d137730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136480 q = 0) : d137731 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136480, d137731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136480, d137731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166954 q = 0) : d167689 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166954, d167689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166954, d167689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166955 q = 0) : d167690 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166955, d167690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166955, d167690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166956 q = 0) : d167691 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166956, d167691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166956, d167691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166957 q = 0) : d167692 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166957, d167692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166957, d167692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15123 (p : Pattern) (selected : d13539 p = 0) : d76229 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13535 q = 0) : d76225 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13535, d76225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13535, d76225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6739 q selected
  have h2 (q : Pattern) (selected : d10243 q = 0) : d69221 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10243, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6739 q selected
    | true =>
      simp only [d10243, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13536 q = 0) : d76226 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13536, d76226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13536, d76226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10245 q = 0) : d69222 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10245, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10245, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13537 q = 0) : d76227 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13537, d76227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13537, d76227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13538 q = 0) : d76228 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13538, d76228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13538, d76228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13539 q = 0) : d76229 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13539, d76229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13539, d76229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro15124 (p : Pattern) (selected : d166963 p = 0) : d167695 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136486 q = 0) : d137709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136486, d137709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136486, d137709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6257 q selected
  have h2 (q : Pattern) (selected : d136487 q = 0) : d137710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136487, d137710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136487, d137710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166959 q = 0) : d167673 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166959, d167673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166959, d167673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15123 q selected
  have h4 (q : Pattern) (selected : d166960 q = 0) : d167674 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166960, d167674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166960, d167674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166961 q = 0) : d167675 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166961, d167675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166961, d167675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136488 q = 0) : d137712 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136488, d137712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136488, d137712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6258 q selected
  have h7 (q : Pattern) (selected : d136489 q = 0) : d137713 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136489, d137713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136489, d137713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136491 q = 0) : d137719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136491, d137719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136491, d137719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d166962 q = 0) : d167694 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166962, d167694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166962, d167694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166963 q = 0) : d167695 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166963, d167695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166963, d167695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15125 (p : Pattern) (selected : d166969 p = 0) : d167701 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166964 q = 0) : d167696 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166964, d167696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15124 q selected
    | true =>
      simp only [d166964, d167696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166965 q = 0) : d167697 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166965, d167697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166965, d167697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136498 q = 0) : d137730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136498, d137730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11794 q selected
    | true =>
      simp only [d136498, d137730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136499 q = 0) : d137731 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136499, d137731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136499, d137731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166966 q = 0) : d167698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166966, d167698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166966, d167698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166967 q = 0) : d167699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166967, d167699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166967, d167699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166968 q = 0) : d167700 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166968, d167700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166968, d167700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166969 q = 0) : d167701 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166969, d167701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166969, d167701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15126 (p : Pattern) (selected : d166973 p = 0) : d167695 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136458 q = 0) : d137709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136458, d137709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136458, d137709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6249 q selected
  have h2 (q : Pattern) (selected : d136459 q = 0) : d137710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136459, d137710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136459, d137710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166938 q = 0) : d167673 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166938, d167673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166938, d167673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15117 q selected
  have h4 (q : Pattern) (selected : d166939 q = 0) : d167674 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166939, d167674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166939, d167674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166940 q = 0) : d167675 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166940, d167675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166940, d167675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136461 q = 0) : d137712 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136461, d137712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136461, d137712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6250 q selected
  have h7 (q : Pattern) (selected : d136462 q = 0) : d137713 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136462, d137713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136462, d137713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136468 q = 0) : d137719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136468, d137719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136468, d137719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d166972 q = 0) : d167694 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166972, d167694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166972, d167694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166973 q = 0) : d167695 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166973, d167695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166973, d167695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15127 (p : Pattern) (selected : d166979 p = 0) : d167707 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166974 q = 0) : d167696 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166974, d167696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15126 q selected
    | true =>
      simp only [d166974, d167696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166975 q = 0) : d167697 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166975, d167697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166975, d167697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166976 q = 0) : d167704 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166976, d167704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166976, d167704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d166977 q = 0) : d167705 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166977, d167705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166977, d167705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d166978 q = 0) : d167706 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166978, d167706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166978, d167706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d166979 q = 0) : d167707 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166979, d167707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166979, d167707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15128 (p : Pattern) (selected : d166985 p = 0) : d167713 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166958 q = 0) : d167693 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166958, d167693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15121 q selected
    | true =>
      simp only [d166958, d167693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15122 q selected
  have h2 (q : Pattern) (selected : d166970 q = 0) : d167702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166970, d167702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15125 q selected
    | true =>
      simp only [d166970, d167702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11796 q selected
  have h3 (q : Pattern) (selected : d166971 q = 0) : d167703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166971, d167703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166971, d167703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166980 q = 0) : d167708 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166980, d167708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15127 q selected
    | true =>
      simp only [d166980, d167708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d166981 q = 0) : d167709 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166981, d167709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166981, d167709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d166982 q = 0) : d167710 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166982, d167710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166982, d167710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166983 q = 0) : d167711 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166983, d167711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166983, d167711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166984 q = 0) : d167712 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166984, d167712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166984, d167712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d166985 q = 0) : d167713 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166985, d167713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166985, d167713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15129 (p : Pattern) (selected : d166991 p = 0) : d167719 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166826 q = 0) : d167575 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166826, d167575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166826, d167575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15093 q selected
  have h2 (q : Pattern) (selected : d166827 q = 0) : d167576 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166827, d167576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166827, d167576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d166835 q = 0) : d167584 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166835, d167584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15093 q selected
    | true =>
      simp only [d166835, d167584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15095 q selected
  have h4 (q : Pattern) (selected : d166836 q = 0) : d167585 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166836, d167585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166836, d167585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d166837 q = 0) : d167586 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166837, d167586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166837, d167586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166916 q = 0) : d167651 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166916, d167651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15107 q selected
    | true =>
      simp only [d166916, d167651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15114 q selected
  have h7 (q : Pattern) (selected : d166923 q = 0) : d167658 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166923, d167658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15115 q selected
    | true =>
      simp only [d166923, d167658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11785 q selected
  have h8 (q : Pattern) (selected : d166924 q = 0) : d167659 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166924, d167659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166924, d167659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d166925 q = 0) : d167660 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166925, d167660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d166925, d167660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d166926 q = 0) : d167661 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166926, d167661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166926, d167661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d166930 q = 0) : d167665 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166930, d167665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166930, d167665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15116 q selected
  have h12 (q : Pattern) (selected : d136451 q = 0) : d137702 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136451, d137702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136451, d137702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11787 q selected
  have h13 (q : Pattern) (selected : d166931 q = 0) : d167666 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166931, d167666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166931, d167666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d166932 q = 0) : d167667 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166932, d167667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d166932, d167667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d166933 q = 0) : d167668 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166933, d167668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d166933, d167668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d166934 q = 0) : d167669 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d166934, d167669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166934, d167669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d166986 q = 0) : d167714 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166986, d167714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166986, d167714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15128 q selected
  have h18 (q : Pattern) (selected : d136538 q = 0) : d137767 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136538, d137767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136538, d137767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11802 q selected
  have h19 (q : Pattern) (selected : d166987 q = 0) : d167715 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166987, d167715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d166987, d167715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d166988 q = 0) : d167716 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166988, d167716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d166988, d167716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d166989 q = 0) : d167717 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166989, d167717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d166989, d167717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d166990 q = 0) : d167718 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d166990, d167718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d166990, d167718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d166991 q = 0) : d167719 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d166991, d167719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d166991, d167719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro15130 (p : Pattern) (selected : d166997 p = 0) : d167725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d166992 q = 0) : d167720 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d166992, d167720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166992, d167720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15129 q selected
  have h2 (q : Pattern) (selected : d166993 q = 0) : d167721 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d166993, d167721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166993, d167721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166994 q = 0) : d167722 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d166994, d167722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166994, d167722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166995 q = 0) : d167723 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d166995, d167723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166995, d167723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166996 q = 0) : d167724 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d166996, d167724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166996, d167724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166997 q = 0) : d167725 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d166997, d167725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166997, d167725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15131 (p : Pattern) (selected : d5251 p = 0) : d69335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5247 q = 0) : d69331 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2828 q selected
    | true =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d5248 q = 0) : d69332 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, d69332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5248, d69332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d5249 q = 0) : d69333 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5249, d69333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5249, d69333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5250 q = 0) : d69334 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5250, d69334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5250, d69334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d5251 q = 0) : d69335 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5251, d69335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d5251, d69335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro15132 (p : Pattern) (selected : d167006 p = 0) : d167734 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136554 q = 0) : d137783 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136554, d137783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136554, d137783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6271 q selected
  have h2 (q : Pattern) (selected : d136555 q = 0) : d137784 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136555, d137784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136555, d137784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167002 q = 0) : d167730 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167002, d167730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167002, d167730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15131 q selected
  have h4 (q : Pattern) (selected : d167003 q = 0) : d167731 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167003, d167731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167003, d167731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167004 q = 0) : d167732 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167004, d167732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167004, d167732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136556 q = 0) : d137785 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136556, d137785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136556, d137785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6272 q selected
  have h7 (q : Pattern) (selected : d136557 q = 0) : d137786 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136557, d137786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136557, d137786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136559 q = 0) : d137788 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136559, d137788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136559, d137788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d167005 q = 0) : d167733 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167005, d167733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167005, d167733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d167006 q = 0) : d167734 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167006, d167734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d167006, d167734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15133 (p : Pattern) (selected : d167012 p = 0) : d167740 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167007 q = 0) : d167735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167007, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15132 q selected
    | true =>
      simp only [d167007, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167008 q = 0) : d167736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167008, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167008, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167009 q = 0) : d167737 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167009, d167737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167009, d167737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167010 q = 0) : d167738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167010, d167738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167010, d167738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d167011 q = 0) : d167739 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167011, d167739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167011, d167739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d167012 q = 0) : d167740 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167012, d167740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167012, d167740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15134 (p : Pattern) (selected : d167018 p = 0) : d167746 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167013 q = 0) : d167741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167013, d167741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15133 q selected
    | true =>
      simp only [d167013, d167741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11808 q selected
  have h2 (q : Pattern) (selected : d167014 q = 0) : d167742 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167014, d167742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167014, d167742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167015 q = 0) : d167743 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167015, d167743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167015, d167743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167016 q = 0) : d167744 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167016, d167744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167016, d167744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167017 q = 0) : d167745 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167017, d167745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167017, d167745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167018 q = 0) : d167746 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167018, d167746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167018, d167746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15135 (p : Pattern) (selected : d167021 p = 0) : d167749 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167007 q = 0) : d167735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167007, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15132 q selected
    | true =>
      simp only [d167007, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167008 q = 0) : d167736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167008, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167008, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167009 q = 0) : d167737 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167009, d167737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167009, d167737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167010 q = 0) : d167738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167010, d167738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167010, d167738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d167011 q = 0) : d167739 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167011, d167739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167011, d167739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d167021 q = 0) : d167749 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167021, d167749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d167021, d167749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15136 (p : Pattern) (selected : d167027 p = 0) : d167755 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167013 q = 0) : d167741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167013, d167741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15133 q selected
    | true =>
      simp only [d167013, d167741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11808 q selected
  have h2 (q : Pattern) (selected : d167014 q = 0) : d167742 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167014, d167742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167014, d167742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167015 q = 0) : d167743 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167015, d167743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167015, d167743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167016 q = 0) : d167744 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167016, d167744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167016, d167744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167017 q = 0) : d167745 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167017, d167745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167017, d167745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167022 q = 0) : d167750 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167022, d167750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15135 q selected
    | true =>
      simp only [d167022, d167750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11811 q selected
  have h7 (q : Pattern) (selected : d167023 q = 0) : d167751 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167023, d167751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167023, d167751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d167024 q = 0) : d167752 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167024, d167752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d167024, d167752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d167025 q = 0) : d167753 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167025, d167753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167025, d167753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d167026 q = 0) : d167754 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167026, d167754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167026, d167754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d167027 q = 0) : d167755 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167027, d167755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167027, d167755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15137 (p : Pattern) (selected : d167032 p = 0) : d167760 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167007 q = 0) : d167735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167007, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15132 q selected
    | true =>
      simp only [d167007, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167008 q = 0) : d167736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167008, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167008, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167009 q = 0) : d167737 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167009, d167737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167009, d167737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167010 q = 0) : d167738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167010, d167738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167010, d167738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d167031 q = 0) : d167759 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167031, d167759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167031, d167759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d167032 q = 0) : d167760 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167032, d167760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167032, d167760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15138 (p : Pattern) (selected : d167039 p = 0) : d167767 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167007 q = 0) : d167735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167007, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15132 q selected
    | true =>
      simp only [d167007, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167008 q = 0) : d167736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167008, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167008, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167009 q = 0) : d167737 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167009, d167737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167009, d167737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167037 q = 0) : d167765 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167037, d167765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167037, d167765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d167038 q = 0) : d167766 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167038, d167766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167038, d167766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d167039 q = 0) : d167767 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167039, d167767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167039, d167767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15139 (p : Pattern) (selected : d13682 p = 0) : d113872 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10353 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10355 q = 0) : d101676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13675 q = 0) : d113865 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13676 q = 0) : d113866 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13678 q = 0) : d113868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8427 q selected
    | true =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13679 q = 0) : d113869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13680 q = 0) : d113870 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, d113870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13680, d113870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13681 q = 0) : d113871 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, d113871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13681, d113871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13682 q = 0) : d113872 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13682, d113872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13682, d113872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15140 (p : Pattern) (selected : d167047 p = 0) : d167775 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136612 q = 0) : d137841 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136612, d137841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136612, d137841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6286 q selected
  have h2 (q : Pattern) (selected : d136613 q = 0) : d137842 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136613, d137842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136613, d137842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167043 q = 0) : d167771 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167043, d167771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167043, d167771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15139 q selected
  have h4 (q : Pattern) (selected : d167044 q = 0) : d167772 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167044, d167772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167044, d167772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167045 q = 0) : d167773 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167045, d167773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167045, d167773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136554 q = 0) : d137783 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136554, d137783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136554, d137783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6271 q selected
  have h7 (q : Pattern) (selected : d136555 q = 0) : d137784 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136555, d137784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136555, d137784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d167002 q = 0) : d167730 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167002, d167730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167002, d167730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15131 q selected
  have h9 (q : Pattern) (selected : d167003 q = 0) : d167731 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167003, d167731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167003, d167731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d167004 q = 0) : d167732 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167004, d167732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d167004, d167732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d167046 q = 0) : d167774 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167046, d167774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167046, d167774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d167047 q = 0) : d167775 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167047, d167775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d167047, d167775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro15141 (p : Pattern) (selected : d167052 p = 0) : d167780 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136554 q = 0) : d137783 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136554, d137783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136554, d137783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6271 q selected
  have h2 (q : Pattern) (selected : d136555 q = 0) : d137784 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136555, d137784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136555, d137784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167002 q = 0) : d167730 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167002, d167730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167002, d167730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15131 q selected
  have h4 (q : Pattern) (selected : d167003 q = 0) : d167731 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167003, d167731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167003, d167731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167004 q = 0) : d167732 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167004, d167732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167004, d167732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167050 q = 0) : d167778 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167050, d167778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167050, d167778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d167051 q = 0) : d167779 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167051, d167779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167051, d167779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d167052 q = 0) : d167780 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167052, d167780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d167052, d167780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15142 (p : Pattern) (selected : d167058 p = 0) : d167786 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167048 q = 0) : d167776 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167048, d167776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15140 q selected
    | true =>
      simp only [d167048, d167776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167049 q = 0) : d167777 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167049, d167777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167049, d167777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167053 q = 0) : d167781 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167053, d167781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15141 q selected
    | true =>
      simp only [d167053, d167781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167054 q = 0) : d167782 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167054, d167782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167054, d167782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167055 q = 0) : d167783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167055, d167783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167055, d167783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167056 q = 0) : d167784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167056, d167784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167056, d167784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d167057 q = 0) : d167785 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167057, d167785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167057, d167785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d167058 q = 0) : d167786 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167058, d167786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167058, d167786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15143 (p : Pattern) (selected : d167062 p = 0) : d167790 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167053 q = 0) : d167781 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167053, d167781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15141 q selected
    | true =>
      simp only [d167053, d167781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167054 q = 0) : d167782 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167054, d167782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167054, d167782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167059 q = 0) : d167787 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167059, d167787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167059, d167787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167060 q = 0) : d167788 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167060, d167788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167060, d167788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d167061 q = 0) : d167789 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167061, d167789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167061, d167789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d167062 q = 0) : d167790 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167062, d167790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167062, d167790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15144 (p : Pattern) (selected : d13712 p = 0) : d69335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10508 q = 0) : d69331 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10508, d69331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6778 q selected
    | true =>
      simp only [d10508, d69331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10510 q = 0) : d69332 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10510, d69332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10510, d69332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13710 q = 0) : d69333 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13710, d69333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13710, d69333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13711 q = 0) : d69334 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13711, d69334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13711, d69334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13712 q = 0) : d69335 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13712, d69335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13712, d69335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro15145 (p : Pattern) (selected : d167068 p = 0) : d167734 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136624 q = 0) : d137783 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136624, d137783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136624, d137783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6291 q selected
  have h2 (q : Pattern) (selected : d136625 q = 0) : d137784 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136625, d137784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136625, d137784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167064 q = 0) : d167730 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167064, d167730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167064, d167730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15144 q selected
  have h4 (q : Pattern) (selected : d167065 q = 0) : d167731 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167065, d167731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167065, d167731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167066 q = 0) : d167732 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167066, d167732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167066, d167732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136626 q = 0) : d137785 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136626, d137785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136626, d137785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6292 q selected
  have h7 (q : Pattern) (selected : d136627 q = 0) : d137786 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136627, d137786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136627, d137786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136629 q = 0) : d137788 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136629, d137788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136629, d137788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d167067 q = 0) : d167733 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167067, d167733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167067, d167733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d167068 q = 0) : d167734 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167068, d167734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d167068, d167734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15146 (p : Pattern) (selected : d167074 p = 0) : d167740 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167069 q = 0) : d167735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167069, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15145 q selected
    | true =>
      simp only [d167069, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167070 q = 0) : d167736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167070, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167070, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136636 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136636, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11820 q selected
    | true =>
      simp only [d136636, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136637 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136637, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136637, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167071 q = 0) : d167737 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167071, d167737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167071, d167737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167072 q = 0) : d167738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167072, d167738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167072, d167738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d167073 q = 0) : d167739 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167073, d167739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167073, d167739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d167074 q = 0) : d167740 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167074, d167740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167074, d167740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15147 (p : Pattern) (selected : d167080 p = 0) : d167796 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167007 q = 0) : d167735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167007, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15132 q selected
    | true =>
      simp only [d167007, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167008 q = 0) : d167736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167008, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167008, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167077 q = 0) : d167793 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167077, d167793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167077, d167793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167078 q = 0) : d167794 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167078, d167794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167078, d167794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167079 q = 0) : d167795 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167079, d167795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167079, d167795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d167080 q = 0) : d167796 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167080, d167796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167080, d167796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15148 (p : Pattern) (selected : d167086 p = 0) : d167802 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167033 q = 0) : d167761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167033, d167761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15137 q selected
    | true =>
      simp only [d167033, d167761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11814 q selected
  have h2 (q : Pattern) (selected : d167034 q = 0) : d167762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167034, d167762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167034, d167762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167035 q = 0) : d167763 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167035, d167763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167035, d167763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167036 q = 0) : d167764 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167036, d167764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167036, d167764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167040 q = 0) : d167768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167040, d167768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15138 q selected
    | true =>
      simp only [d167040, d167768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11816 q selected
  have h6 (q : Pattern) (selected : d167041 q = 0) : d167769 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167041, d167769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167041, d167769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d167042 q = 0) : d167770 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167042, d167770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167042, d167770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d167063 q = 0) : d167791 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167063, d167791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15142 q selected
    | true =>
      simp only [d167063, d167791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15143 q selected
  have h9 (q : Pattern) (selected : d167075 q = 0) : d167741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167075, d167741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15146 q selected
    | true =>
      simp only [d167075, d167741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11822 q selected
  have h10 (q : Pattern) (selected : d167076 q = 0) : d167792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167076, d167792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d167076, d167792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d167081 q = 0) : d167797 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167081, d167797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15147 q selected
    | true =>
      simp only [d167081, d167797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d167082 q = 0) : d167798 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167082, d167798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d167082, d167798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d167083 q = 0) : d167799 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167083, d167799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d167083, d167799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d167084 q = 0) : d167800 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167084, d167800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d167084, d167800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d167085 q = 0) : d167801 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167085, d167801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167085, d167801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d167086 q = 0) : d167802 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167086, d167802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167086, d167802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro15149 (p : Pattern) (selected : d167087 p = 0) : d167803 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167007 q = 0) : d167735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167007, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15132 q selected
    | true =>
      simp only [d167007, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167008 q = 0) : d167736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167008, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167008, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167009 q = 0) : d167737 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167009, d167737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167009, d167737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167010 q = 0) : d167738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167010, d167738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167010, d167738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d167031 q = 0) : d167759 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167031, d167759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167031, d167759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d167087 q = 0) : d167803 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167087, d167803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d167087, d167803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15150 (p : Pattern) (selected : d167092 p = 0) : d167808 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167007 q = 0) : d167735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167007, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15132 q selected
    | true =>
      simp only [d167007, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167008 q = 0) : d167736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167008, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167008, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167009 q = 0) : d167737 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167009, d167737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167009, d167737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167037 q = 0) : d167765 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167037, d167765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167037, d167765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d167038 q = 0) : d167766 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167038, d167766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167038, d167766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d167092 q = 0) : d167808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167092, d167808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d167092, d167808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15151 (p : Pattern) (selected : d167096 p = 0) : d167812 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167048 q = 0) : d167776 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167048, d167776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15140 q selected
    | true =>
      simp only [d167048, d167776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167049 q = 0) : d167777 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167049, d167777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167049, d167777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167053 q = 0) : d167781 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167053, d167781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15141 q selected
    | true =>
      simp only [d167053, d167781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167054 q = 0) : d167782 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167054, d167782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167054, d167782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167055 q = 0) : d167783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167055, d167783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167055, d167783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167056 q = 0) : d167784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167056, d167784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167056, d167784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d167057 q = 0) : d167785 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167057, d167785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167057, d167785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d167096 q = 0) : d167812 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167096, d167812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d167096, d167812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15152 (p : Pattern) (selected : d167097 p = 0) : d167813 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167053 q = 0) : d167781 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167053, d167781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15141 q selected
    | true =>
      simp only [d167053, d167781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167054 q = 0) : d167782 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167054, d167782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167054, d167782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167059 q = 0) : d167787 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167059, d167787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167059, d167787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167060 q = 0) : d167788 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167060, d167788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167060, d167788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d167061 q = 0) : d167789 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167061, d167789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167061, d167789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d167097 q = 0) : d167813 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167097, d167813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d167097, d167813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15153 (p : Pattern) (selected : d167099 p = 0) : d167749 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167069 q = 0) : d167735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167069, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15145 q selected
    | true =>
      simp only [d167069, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167070 q = 0) : d167736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167070, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167070, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136636 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136636, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11820 q selected
    | true =>
      simp only [d136636, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136637 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136637, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136637, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167071 q = 0) : d167737 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167071, d167737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167071, d167737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167072 q = 0) : d167738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167072, d167738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167072, d167738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d167073 q = 0) : d167739 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167073, d167739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167073, d167739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d167099 q = 0) : d167749 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167099, d167749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d167099, d167749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15154 (p : Pattern) (selected : d167102 p = 0) : d167816 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167007 q = 0) : d167735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167007, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15132 q selected
    | true =>
      simp only [d167007, d167735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167008 q = 0) : d167736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167008, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167008, d167736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167077 q = 0) : d167793 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167077, d167793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167077, d167793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167078 q = 0) : d167794 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167078, d167794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167078, d167794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167079 q = 0) : d167795 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167079, d167795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167079, d167795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d167102 q = 0) : d167816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167102, d167816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167102, d167816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15155 (p : Pattern) (selected : d167108 p = 0) : d167822 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167033 q = 0) : d167761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167033, d167761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15137 q selected
    | true =>
      simp only [d167033, d167761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11814 q selected
  have h2 (q : Pattern) (selected : d167034 q = 0) : d167762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167034, d167762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167034, d167762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167035 q = 0) : d167763 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167035, d167763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167035, d167763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167036 q = 0) : d167764 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167036, d167764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167036, d167764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167040 q = 0) : d167768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167040, d167768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15138 q selected
    | true =>
      simp only [d167040, d167768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11816 q selected
  have h6 (q : Pattern) (selected : d167041 q = 0) : d167769 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167041, d167769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167041, d167769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d167042 q = 0) : d167770 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167042, d167770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167042, d167770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d167063 q = 0) : d167791 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167063, d167791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15142 q selected
    | true =>
      simp only [d167063, d167791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15143 q selected
  have h9 (q : Pattern) (selected : d167075 q = 0) : d167741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167075, d167741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15146 q selected
    | true =>
      simp only [d167075, d167741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11822 q selected
  have h10 (q : Pattern) (selected : d167076 q = 0) : d167792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167076, d167792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d167076, d167792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d167081 q = 0) : d167797 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167081, d167797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15147 q selected
    | true =>
      simp only [d167081, d167797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d167082 q = 0) : d167798 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167082, d167798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d167082, d167798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d167083 q = 0) : d167799 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167083, d167799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d167083, d167799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d167084 q = 0) : d167800 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167084, d167800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d167084, d167800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d167085 q = 0) : d167801 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167085, d167801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167085, d167801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d167088 q = 0) : d167804 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167088, d167804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15149 q selected
    | true =>
      simp only [d167088, d167804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11828 q selected
  have h17 (q : Pattern) (selected : d167089 q = 0) : d167805 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167089, d167805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167089, d167805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d167090 q = 0) : d167806 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167090, d167806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d167090, d167806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d167091 q = 0) : d167807 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167091, d167807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167091, d167807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d167093 q = 0) : d167809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167093, d167809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15150 q selected
    | true =>
      simp only [d167093, d167809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11830 q selected
  have h21 (q : Pattern) (selected : d167094 q = 0) : d167810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167094, d167810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167094, d167810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d167095 q = 0) : d167811 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167095, d167811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d167095, d167811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d167098 q = 0) : d167814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167098, d167814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15151 q selected
    | true =>
      simp only [d167098, d167814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15152 q selected
  have h24 (q : Pattern) (selected : d167100 q = 0) : d167750 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167100, d167750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15153 q selected
    | true =>
      simp only [d167100, d167750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11833 q selected
  have h25 (q : Pattern) (selected : d167101 q = 0) : d167815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167101, d167815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d167101, d167815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d167103 q = 0) : d167817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167103, d167817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15154 q selected
    | true =>
      simp only [d167103, d167817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d167104 q = 0) : d167818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167104, d167818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d167104, d167818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d167105 q = 0) : d167819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167105, d167819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d167105, d167819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d167106 q = 0) : d167820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167106, d167820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d167106, d167820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d167107 q = 0) : d167821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167107, d167821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d167107, d167821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d167108 q = 0) : d167822 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167108, d167822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d167108, d167822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro15156 (p : Pattern) (selected : d167115 p = 0) : d167829 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167110 q = 0) : d167824 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167110, d167824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15143 q selected
    | true =>
      simp only [d167110, d167824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11808 q selected
  have h2 (q : Pattern) (selected : d167111 q = 0) : d167825 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167111, d167825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167111, d167825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167112 q = 0) : d167826 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167112, d167826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167112, d167826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167113 q = 0) : d167827 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167113, d167827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167113, d167827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167114 q = 0) : d167828 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167114, d167828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167114, d167828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136690 q = 0) : d137893 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136690, d137893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11808 q selected
    | true =>
      simp only [d136690, d137893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136691 q = 0) : d137894 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136691, d137894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136691, d137894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136692 q = 0) : d137895 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136692, d137895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136692, d137895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d136693 q = 0) : d137896 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136693, d137896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136693, d137896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136694 q = 0) : d137897 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136694, d137897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136694, d137897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d167115 q = 0) : d167829 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167115, d167829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167115, d167829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15157 (p : Pattern) (selected : d167122 p = 0) : d167836 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167098 q = 0) : d167814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167098, d167814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15151 q selected
    | true =>
      simp only [d167098, d167814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15152 q selected
  have h2 (q : Pattern) (selected : d167100 q = 0) : d167750 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167100, d167750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15153 q selected
    | true =>
      simp only [d167100, d167750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11833 q selected
  have h3 (q : Pattern) (selected : d167101 q = 0) : d167815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167101, d167815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167101, d167815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d167103 q = 0) : d167817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167103, d167817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15154 q selected
    | true =>
      simp only [d167103, d167817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167104 q = 0) : d167818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167104, d167818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167104, d167818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d167105 q = 0) : d167819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167105, d167819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167105, d167819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d167120 q = 0) : d167834 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167120, d167834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167120, d167834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d167121 q = 0) : d167835 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167121, d167835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167121, d167835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d167122 q = 0) : d167836 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167122, d167836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167122, d167836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15158 (p : Pattern) (selected : d6647 p = 0) : d76365 p = 1 := by
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
  have h6 (q : Pattern) (selected : d6646 q = 0) : d76364 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6646, d76364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6646, d76364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d6647 q = 0) : d76365 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6647, d76365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6647, d76365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro15159 (p : Pattern) (selected : d13821 p = 0) : d113973 p = 1 := by
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
  have h6 (q : Pattern) (selected : d13816 q = 0) : d113968 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13817 q = 0) : d113969 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, d113969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13817, d113969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8427 q selected
  have h8 (q : Pattern) (selected : d13678 q = 0) : d113868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8427 q selected
    | true =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13818 q = 0) : d113970 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, d113970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13818, d113970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13679 q = 0) : d113869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d13819 q = 0) : d113971 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, d113971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13819, d113971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d13820 q = 0) : d113972 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, d113972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d13820, d113972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d13821 q = 0) : d113973 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13821, d113973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13821, d113973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro15160 (p : Pattern) (selected : d167135 p = 0) : d167849 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136716 q = 0) : d137919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136716, d137919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136716, d137919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6314 q selected
  have h2 (q : Pattern) (selected : d136717 q = 0) : d137920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136717, d137920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136717, d137920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167128 q = 0) : d167842 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167128, d167842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167128, d167842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15159 q selected
  have h4 (q : Pattern) (selected : d167129 q = 0) : d167843 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167129, d167843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167129, d167843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167130 q = 0) : d167844 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167130, d167844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167130, d167844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136718 q = 0) : d137921 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136718, d137921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136718, d137921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6315 q selected
  have h7 (q : Pattern) (selected : d136719 q = 0) : d137922 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136719, d137922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136719, d137922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d167131 q = 0) : d167845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167131, d167845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167131, d167845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15158 q selected
  have h9 (q : Pattern) (selected : d167132 q = 0) : d167846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167132, d167846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167132, d167846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d167133 q = 0) : d167847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167133, d167847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d167133, d167847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d167134 q = 0) : d167848 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167134, d167848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167134, d167848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d167135 q = 0) : d167849 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167135, d167849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d167135, d167849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro15161 (p : Pattern) (selected : d167140 p = 0) : d167854 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136718 q = 0) : d137921 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136718, d137921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136718, d137921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6315 q selected
  have h2 (q : Pattern) (selected : d136719 q = 0) : d137922 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136719, d137922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136719, d137922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167131 q = 0) : d167845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167131, d167845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167131, d167845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15158 q selected
  have h4 (q : Pattern) (selected : d167132 q = 0) : d167846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167132, d167846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167132, d167846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167133 q = 0) : d167847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167133, d167847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167133, d167847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167138 q = 0) : d167852 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167138, d167852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167138, d167852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d167139 q = 0) : d167853 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167139, d167853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167139, d167853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d167140 q = 0) : d167854 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167140, d167854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d167140, d167854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15162 (p : Pattern) (selected : d167146 p = 0) : d167860 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167136 q = 0) : d167850 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167136, d167850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15160 q selected
    | true =>
      simp only [d167136, d167850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167137 q = 0) : d167851 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167137, d167851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167137, d167851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167141 q = 0) : d167855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167141, d167855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15161 q selected
    | true =>
      simp only [d167141, d167855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167142 q = 0) : d167856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167142, d167856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167142, d167856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167143 q = 0) : d167857 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167143, d167857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167143, d167857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167144 q = 0) : d167858 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167144, d167858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167144, d167858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d167145 q = 0) : d167859 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167145, d167859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167145, d167859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d167146 q = 0) : d167860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167146, d167860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d167146, d167860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15163 (p : Pattern) (selected : d167150 p = 0) : d167864 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167141 q = 0) : d167855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167141, d167855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15161 q selected
    | true =>
      simp only [d167141, d167855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167142 q = 0) : d167856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167142, d167856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167142, d167856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136739 q = 0) : d137942 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136739, d137942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11843 q selected
    | true =>
      simp only [d136739, d137942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136740 q = 0) : d137943 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136740, d137943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136740, d137943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167147 q = 0) : d167861 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167147, d167861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167147, d167861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167148 q = 0) : d167862 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167148, d167862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167148, d167862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d167149 q = 0) : d167863 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167149, d167863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167149, d167863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d167150 q = 0) : d167864 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167150, d167864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d167150, d167864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15164 (p : Pattern) (selected : d13866 p = 0) : d76365 p = 1 := by
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
  have h6 (q : Pattern) (selected : d13865 q = 0) : d76364 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13865, d76364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13865, d76364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13866 q = 0) : d76365 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13866, d76365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13866, d76365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro15165 (p : Pattern) (selected : d167156 p = 0) : d167867 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136746 q = 0) : d137921 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136746, d137921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136746, d137921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6323 q selected
  have h2 (q : Pattern) (selected : d136747 q = 0) : d137922 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136747, d137922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136747, d137922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167152 q = 0) : d167845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167152, d167845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167152, d167845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15164 q selected
  have h4 (q : Pattern) (selected : d167153 q = 0) : d167846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167153, d167846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167153, d167846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167154 q = 0) : d167847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167154, d167847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167154, d167847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136748 q = 0) : d137924 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136748, d137924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136748, d137924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6324 q selected
  have h7 (q : Pattern) (selected : d136749 q = 0) : d137925 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136749, d137925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136749, d137925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136751 q = 0) : d137931 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136751, d137931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136751, d137931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d167155 q = 0) : d167866 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167155, d167866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167155, d167866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d167156 q = 0) : d167867 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167156, d167867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d167156, d167867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15166 (p : Pattern) (selected : d167162 p = 0) : d167873 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167157 q = 0) : d167868 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167157, d167868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15165 q selected
    | true =>
      simp only [d167157, d167868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167158 q = 0) : d167869 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167158, d167869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167158, d167869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136758 q = 0) : d137942 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136758, d137942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11846 q selected
    | true =>
      simp only [d136758, d137942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136759 q = 0) : d137943 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136759, d137943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136759, d137943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167159 q = 0) : d167870 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167159, d167870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167159, d167870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167160 q = 0) : d167871 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167160, d167871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167160, d167871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d167161 q = 0) : d167872 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167161, d167872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167161, d167872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d167162 q = 0) : d167873 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167162, d167873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d167162, d167873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15167 (p : Pattern) (selected : d167166 p = 0) : d167867 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136718 q = 0) : d137921 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136718, d137921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136718, d137921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6315 q selected
  have h2 (q : Pattern) (selected : d136719 q = 0) : d137922 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136719, d137922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136719, d137922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167131 q = 0) : d167845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167131, d167845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167131, d167845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15158 q selected
  have h4 (q : Pattern) (selected : d167132 q = 0) : d167846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167132, d167846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167132, d167846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167133 q = 0) : d167847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167133, d167847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167133, d167847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136721 q = 0) : d137924 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136721, d137924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136721, d137924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6316 q selected
  have h7 (q : Pattern) (selected : d136722 q = 0) : d137925 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136722, d137925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136722, d137925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136728 q = 0) : d137931 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136728, d137931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136728, d137931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d167165 q = 0) : d167866 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167165, d167866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167165, d167866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d167166 q = 0) : d167867 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167166, d167867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d167166, d167867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15168 (p : Pattern) (selected : d167172 p = 0) : d167879 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167167 q = 0) : d167868 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167167, d167868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15167 q selected
    | true =>
      simp only [d167167, d167868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167168 q = 0) : d167869 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167168, d167869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167168, d167869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167169 q = 0) : d167876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167169, d167876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167169, d167876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167170 q = 0) : d167877 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167170, d167877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167170, d167877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167171 q = 0) : d167878 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167171, d167878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167171, d167878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d167172 q = 0) : d167879 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167172, d167879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167172, d167879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15169 (p : Pattern) (selected : d167178 p = 0) : d167885 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167151 q = 0) : d167865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167151, d167865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15162 q selected
    | true =>
      simp only [d167151, d167865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15163 q selected
  have h2 (q : Pattern) (selected : d167163 q = 0) : d167874 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167163, d167874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15166 q selected
    | true =>
      simp only [d167163, d167874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11848 q selected
  have h3 (q : Pattern) (selected : d167164 q = 0) : d167875 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167164, d167875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167164, d167875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d167173 q = 0) : d167880 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167173, d167880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15168 q selected
    | true =>
      simp only [d167173, d167880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167174 q = 0) : d167881 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167174, d167881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167174, d167881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d167175 q = 0) : d167882 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167175, d167882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167175, d167882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d167176 q = 0) : d167883 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167176, d167883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167176, d167883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d167177 q = 0) : d167884 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167177, d167884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167177, d167884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d167178 q = 0) : d167885 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167178, d167885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167178, d167885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15170 (p : Pattern) (selected : d167184 p = 0) : d167891 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167019 q = 0) : d167747 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167019, d167747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167019, d167747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15134 q selected
  have h2 (q : Pattern) (selected : d167020 q = 0) : d167748 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167020, d167748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167020, d167748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d167028 q = 0) : d167756 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167028, d167756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15134 q selected
    | true =>
      simp only [d167028, d167756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15136 q selected
  have h4 (q : Pattern) (selected : d167029 q = 0) : d167757 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167029, d167757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167029, d167757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167030 q = 0) : d167758 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167030, d167758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167030, d167758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167109 q = 0) : d167823 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167109, d167823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15148 q selected
    | true =>
      simp only [d167109, d167823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15155 q selected
  have h7 (q : Pattern) (selected : d167116 q = 0) : d167830 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167116, d167830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15156 q selected
    | true =>
      simp only [d167116, d167830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11837 q selected
  have h8 (q : Pattern) (selected : d167117 q = 0) : d167831 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167117, d167831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167117, d167831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d167118 q = 0) : d167832 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167118, d167832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d167118, d167832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d167119 q = 0) : d167833 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167119, d167833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167119, d167833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d167123 q = 0) : d167837 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167123, d167837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167123, d167837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15157 q selected
  have h12 (q : Pattern) (selected : d136711 q = 0) : d137914 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136711, d137914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136711, d137914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11839 q selected
  have h13 (q : Pattern) (selected : d167124 q = 0) : d167838 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167124, d167838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d167124, d167838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d167125 q = 0) : d167839 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167125, d167839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d167125, d167839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d167126 q = 0) : d167840 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167126, d167840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d167126, d167840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d167127 q = 0) : d167841 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167127, d167841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d167127, d167841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d167179 q = 0) : d167886 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167179, d167886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167179, d167886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15169 q selected
  have h18 (q : Pattern) (selected : d136798 q = 0) : d137979 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136798, d137979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136798, d137979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11854 q selected
  have h19 (q : Pattern) (selected : d167180 q = 0) : d167887 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167180, d167887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d167180, d167887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d167181 q = 0) : d167888 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167181, d167888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d167181, d167888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d167182 q = 0) : d167889 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167182, d167889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d167182, d167889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d167183 q = 0) : d167890 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167183, d167890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d167183, d167890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d167184 q = 0) : d167891 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d167184, d167891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d167184, d167891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro15171 (p : Pattern) (selected : d167190 p = 0) : d167897 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167185 q = 0) : d167892 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d167185, d167892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167185, d167892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15170 q selected
  have h2 (q : Pattern) (selected : d167186 q = 0) : d167893 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d167186, d167893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167186, d167893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167187 q = 0) : d167894 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d167187, d167894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167187, d167894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d167188 q = 0) : d167895 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d167188, d167895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167188, d167895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167189 q = 0) : d167896 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d167189, d167896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167189, d167896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167190 q = 0) : d167897 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d167190, d167897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167190, d167897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15172 (p : Pattern) (selected : d167196 p = 0) : d167903 p = 1 := by
  have h0 (q : Pattern) (selected : d166534 q = 0) : d167304 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d166534, d167304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11620 q selected
    | true =>
      simp only [d166534, d167304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15032 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d166615 q = 0) : d167385 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d166615, d167385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166615, d167385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15048 q selected
  have h3 (q : Pattern) (selected : d166616 q = 0) : d167386 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d166616, d167386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166616, d167386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166806 q = 0) : d167555 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d166806, d167555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166806, d167555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15089 q selected
  have h5 (q : Pattern) (selected : d166807 q = 0) : d167556 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d166807, d167556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166807, d167556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166808 q = 0) : d167557 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d166808, d167557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166808, d167557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166998 q = 0) : d167726 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d166998, d167726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166998, d167726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15130 q selected
  have h8 (q : Pattern) (selected : d166999 q = 0) : d167727 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d166999, d167727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166999, d167727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d167000 q = 0) : d167728 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d167000, d167728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167000, d167728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d167001 q = 0) : d167729 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d167001, d167729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167001, d167729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d167191 q = 0) : d167898 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d167191, d167898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167191, d167898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15171 q selected
  have h12 (q : Pattern) (selected : d167192 q = 0) : d167899 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d167192, d167899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167192, d167899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d167193 q = 0) : d167900 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d167193, d167900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167193, d167900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d167194 q = 0) : d167901 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d167194, d167901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167194, d167901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d167195 q = 0) : d167902 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d167195, d167902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d167195, d167902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d167196 q = 0) : d167903 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d167196, d167903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d167196, d167903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro15173 (p : Pattern) (selected : d167202 p = 0) : d167909 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167197 q = 0) : d167904 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d167197, d167904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15172 q selected
    | true =>
      simp only [d167197, d167904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167198 q = 0) : d167905 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d167198, d167905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167198, d167905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d167199 q = 0) : d167906 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d167199, d167906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167199, d167906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167200 q = 0) : d167907 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d167200, d167907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167200, d167907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167201 q = 0) : d167908 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d167201, d167908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167201, d167908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d167202 q = 0) : d167909 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d167202, d167909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167202, d167909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15174 (p : Pattern) (selected : d167208 p = 0) : d167915 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167203 q = 0) : d167910 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d167203, d167910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15173 q selected
    | true =>
      simp only [d167203, d167910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167204 q = 0) : d167911 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d167204, d167911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167204, d167911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d167205 q = 0) : d167912 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d167205, d167912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167205, d167912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167206 q = 0) : d167913 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d167206, d167913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167206, d167913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167207 q = 0) : d167914 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d167207, d167914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167207, d167914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d167208 q = 0) : d167915 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d167208, d167915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167208, d167915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15175 (p : Pattern) (selected : d167214 p = 0) : d167921 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167209 q = 0) : d167916 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d167209, d167916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15174 q selected
    | true =>
      simp only [d167209, d167916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167210 q = 0) : d167917 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d167210, d167917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167210, d167917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d167211 q = 0) : d167918 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d167211, d167918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167211, d167918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167212 q = 0) : d167919 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d167212, d167919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167212, d167919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167213 q = 0) : d167920 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d167213, d167920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167213, d167920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d167214 q = 0) : d167921 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d167214, d167921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167214, d167921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15176 (p : Pattern) (selected : d167220 p = 0) : d167927 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167215 q = 0) : d167922 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d167215, d167922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15175 q selected
    | true =>
      simp only [d167215, d167922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167216 q = 0) : d167923 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d167216, d167923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167216, d167923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d167217 q = 0) : d167924 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d167217, d167924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167217, d167924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167218 q = 0) : d167925 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d167218, d167925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167218, d167925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167219 q = 0) : d167926 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d167219, d167926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167219, d167926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d167220 q = 0) : d167927 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d167220, d167927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167220, d167927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15177 (p : Pattern) (selected : d167226 p = 0) : d167933 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167221 q = 0) : d167928 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d167221, d167928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15176 q selected
    | true =>
      simp only [d167221, d167928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167222 q = 0) : d167929 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d167222, d167929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167222, d167929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d167223 q = 0) : d167930 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d167223, d167930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167223, d167930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167224 q = 0) : d167931 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d167224, d167931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167224, d167931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167225 q = 0) : d167932 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d167225, d167932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167225, d167932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d167226 q = 0) : d167933 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d167226, d167933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167226, d167933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15178 (p : Pattern) (selected : d167232 p = 0) : d167939 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167227 q = 0) : d167934 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d167227, d167934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15177 q selected
    | true =>
      simp only [d167227, d167934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167228 q = 0) : d167935 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d167228, d167935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167228, d167935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d167229 q = 0) : d167936 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d167229, d167936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167229, d167936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167230 q = 0) : d167937 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d167230, d167937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167230, d167937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167231 q = 0) : d167938 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d167231, d167938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167231, d167938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d167232 q = 0) : d167939 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d167232, d167939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167232, d167939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15179 (p : Pattern) (selected : d167238 p = 0) : d167945 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d167233 q = 0) : d167940 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d167233, d167940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15178 q selected
    | true =>
      simp only [d167233, d167940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167234 q = 0) : d167941 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d167234, d167941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167234, d167941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d167235 q = 0) : d167942 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d167235, d167942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167235, d167942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167236 q = 0) : d167943 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d167236, d167943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167236, d167943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167237 q = 0) : d167944 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d167237, d167944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167237, d167944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d167238 q = 0) : d167945 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d167238, d167945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167238, d167945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15180 (p : Pattern) (selected : d166485 p = 1) : d169136 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135644 q = 1) : d135644 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d135650 q = 1) : d135650 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d166480 q = 1) : d166480 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d135674 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11877 q selected
    | true =>
      simp only [d135674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11866 q selected
  have h5 (q : Pattern) (selected : d166481 q = 1) : d169132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166481, d169132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166481, d169132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135681 q = 1) : d135681 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d166482 q = 1) : d169133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166482, d169133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166482, d169133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166483 q = 1) : d169134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166483, d169134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166483, d169134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d166484 q = 1) : d169135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166484, d169135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166484, d169135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166485 q = 1) : d169136 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166485, d169136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166485, d169136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro15181 (p : Pattern) (selected : d166492 p = 1) : d169141 p = 1 := by
  have h0 (q : Pattern) (selected : d135644 q = 1) : d135644 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135650 q = 1) : d135650 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d166480 q = 1) : d166480 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d135674 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11877 q selected
    | true =>
      simp only [d135674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11866 q selected
  have h4 (q : Pattern) (selected : d166481 q = 1) : d169132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166481, d169132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166481, d169132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135681 q = 1) : d135681 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d166482 q = 1) : d169133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166482, d169133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166482, d169133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166483 q = 1) : d169134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166483, d169134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166483, d169134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166484 q = 1) : d169135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166484, d169135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166484, d169135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135690 q = 1) : d135690 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d135694 q = 1) : d135694 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d166487 q = 1) : d166487 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d135698 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11879 q selected
    | true =>
      simp only [d135698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11868 q selected
  have h13 (q : Pattern) (selected : d166488 q = 1) : d169137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166488, d169137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166488, d169137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d135702 q = 1) : d135702 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d166489 q = 1) : d169138 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166489, d169138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d166489, d169138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d166490 q = 1) : d169139 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166490, d169139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166490, d169139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d166491 q = 1) : d169140 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166491, d169140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166491, d169140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d166492 q = 1) : d169141 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166492, d169141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d166492, d169141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro15182 (p : Pattern) (selected : d166499 p = 1) : d169148 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166487 q = 1) : d166487 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d135698 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11879 q selected
    | true =>
      simp only [d135698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11868 q selected
  have h3 (q : Pattern) (selected : d166488 q = 1) : d169137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166488, d169137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166488, d169137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d135702 q = 1) : d135702 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d166489 q = 1) : d169138 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166489, d169138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166489, d169138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166497 q = 1) : d169146 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166497, d169146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166497, d169146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166498 q = 1) : d169147 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166498, d169147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166498, d169147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166499 q = 1) : d169148 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166499, d169148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166499, d169148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15183 (p : Pattern) (selected : d166521 p = 1) : d169158 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166516 q = 1) : d166516 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d135746 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11883 q selected
    | true =>
      simp only [d135746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11872 q selected
  have h3 (q : Pattern) (selected : d166517 q = 1) : d169154 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166517, d169154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166517, d169154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d135753 q = 1) : d135753 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d166518 q = 1) : d169155 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166518, d169155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166518, d169155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166519 q = 1) : d169156 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166519, d169156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166519, d169156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166520 q = 1) : d169157 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166520, d169157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166520, d169157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166521 q = 1) : d169158 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166521, d169158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166521, d169158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15184 (p : Pattern) (selected : d166527 p = 1) : d169164 p = 1 := by
  have h0 (q : Pattern) (selected : d135638 q = 1) : d135638 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166493 q = 1) : d169142 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166493, d169142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15180 q selected
    | true =>
      simp only [d166493, d169142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15181 q selected
  have h2 (q : Pattern) (selected : d135709 q = 1) : d135709 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d166494 q = 1) : d169143 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166494, d169143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166494, d169143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d166495 q = 1) : d169144 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166495, d169144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166495, d169144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166496 q = 1) : d169145 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166496, d169145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166496, d169145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166500 q = 1) : d169149 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166500, d169149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166500, d169149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15182 q selected
  have h8 (q : Pattern) (selected : d135718 q = 1) : d135718 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d166501 q = 1) : d169150 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166501, d169150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166501, d169150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166502 q = 1) : d169151 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166502, d169151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166502, d169151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d166503 q = 1) : d169152 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166503, d169152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166503, d169152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d166504 q = 1) : d169153 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d166504, d169153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166504, d169153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d166522 q = 1) : d169159 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166522, d169159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166522, d169159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15183 q selected
  have h14 (q : Pattern) (selected : d135764 q = 1) : d135764 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d166523 q = 1) : d169160 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166523, d169160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d166523, d169160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d166524 q = 1) : d169161 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166524, d169161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d166524, d169161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d166525 q = 1) : d169162 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166525, d169162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d166525, d169162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d166526 q = 1) : d169163 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d166526, d169163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d166526, d169163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d166527 q = 1) : d169164 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d166527, d169164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d166527, d169164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro15185 (p : Pattern) (selected : d166533 p = 1) : d169170 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166528 q = 1) : d169165 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d166528, d169165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166528, d169165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15184 q selected
  have h2 (q : Pattern) (selected : d166529 q = 1) : d169166 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d166529, d169166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166529, d169166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166530 q = 1) : d169167 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d166530, d169167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166530, d169167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166531 q = 1) : d169168 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d166531, d169168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166531, d169168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166532 q = 1) : d169169 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d166532, d169169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166532, d169169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166533 q = 1) : d169170 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d166533, d169170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166533, d169170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15186 (p : Pattern) (selected : d166557 p = 1) : d169176 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135825 q = 1) : d135825 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d135834 q = 1) : d135834 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d166546 q = 1) : d166546 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d135869 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11889 q selected
    | true =>
      simp only [d135869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11890 q selected
  have h5 (q : Pattern) (selected : d166547 q = 1) : d169172 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166547, d169172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166547, d169172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166553 q = 1) : d166553 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d166554 q = 1) : d169173 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166554, d169173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166554, d169173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166555 q = 1) : d169174 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166555, d169174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166555, d169174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d166556 q = 1) : d169175 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166556, d169175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166556, d169175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166557 q = 1) : d169176 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166557, d169176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166557, d169176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro15187 (p : Pattern) (selected : d166567 p = 1) : d169181 p = 1 := by
  have h0 (q : Pattern) (selected : d135825 q = 1) : d135825 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135834 q = 1) : d135834 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d166546 q = 1) : d166546 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d135869 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11889 q selected
    | true =>
      simp only [d135869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11890 q selected
  have h4 (q : Pattern) (selected : d166547 q = 1) : d169172 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166547, d169172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166547, d169172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166553 q = 1) : d166553 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d166554 q = 1) : d169173 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166554, d169173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166554, d169173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166555 q = 1) : d169174 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166555, d169174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166555, d169174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166556 q = 1) : d169175 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166556, d169175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166556, d169175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135893 q = 1) : d135893 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d135898 q = 1) : d135898 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d166559 q = 1) : d166559 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d135903 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11892 q selected
    | true =>
      simp only [d135903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11893 q selected
  have h13 (q : Pattern) (selected : d166560 q = 1) : d169177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166560, d169177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166560, d169177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d166563 q = 1) : d166563 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d166564 q = 1) : d169178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166564, d169178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d166564, d169178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d166565 q = 1) : d169179 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166565, d169179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166565, d169179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d166566 q = 1) : d169180 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166566, d169180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166566, d169180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d166567 q = 1) : d169181 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166567, d169181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d166567, d169181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro15188 (p : Pattern) (selected : d166574 p = 1) : d169188 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166559 q = 1) : d166559 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d135903 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11892 q selected
    | true =>
      simp only [d135903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11893 q selected
  have h3 (q : Pattern) (selected : d166560 q = 1) : d169177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166560, d169177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166560, d169177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166563 q = 1) : d166563 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d166564 q = 1) : d169178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166564, d169178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166564, d169178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166572 q = 1) : d169186 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166572, d169186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166572, d169186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166573 q = 1) : d169187 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166573, d169187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166573, d169187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166574 q = 1) : d169188 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166574, d169188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166574, d169188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15189 (p : Pattern) (selected : d166602 p = 1) : d169198 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166591 q = 1) : d166591 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d135991 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11898 q selected
    | true =>
      simp only [d135991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11899 q selected
  have h3 (q : Pattern) (selected : d166592 q = 1) : d169194 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166592, d169194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166592, d169194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166598 q = 1) : d166598 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d166599 q = 1) : d169195 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166599, d169195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166599, d169195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166600 q = 1) : d169196 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166600, d169196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166600, d169196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166601 q = 1) : d169197 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166601, d169197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166601, d169197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166602 q = 1) : d169198 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166602, d169198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166602, d169198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15190 (p : Pattern) (selected : d166608 p = 1) : d169204 p = 1 := by
  have h0 (q : Pattern) (selected : d135817 q = 1) : d135817 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166568 q = 1) : d169182 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166568, d169182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15186 q selected
    | true =>
      simp only [d166568, d169182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15187 q selected
  have h2 (q : Pattern) (selected : d135925 q = 1) : d135925 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d166569 q = 1) : d169183 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166569, d169183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166569, d169183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d166570 q = 1) : d169184 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166570, d169184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166570, d169184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166571 q = 1) : d169185 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166571, d169185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166571, d169185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166575 q = 1) : d169189 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166575, d169189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166575, d169189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15188 q selected
  have h8 (q : Pattern) (selected : d135934 q = 1) : d135934 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d166576 q = 1) : d169190 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166576, d169190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166576, d169190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166577 q = 1) : d169191 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166577, d169191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166577, d169191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d166578 q = 1) : d169192 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166578, d169192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166578, d169192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d166579 q = 1) : d169193 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d166579, d169193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166579, d169193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d166603 q = 1) : d169199 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166603, d169199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166603, d169199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15189 q selected
  have h14 (q : Pattern) (selected : d136021 q = 1) : d136021 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d166604 q = 1) : d169200 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166604, d169200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d166604, d169200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d166605 q = 1) : d169201 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166605, d169201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d166605, d169201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d166606 q = 1) : d169202 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166606, d169202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d166606, d169202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d166607 q = 1) : d169203 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d166607, d169203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d166607, d169203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d166608 q = 1) : d169204 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d166608, d169204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d166608, d169204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro15191 (p : Pattern) (selected : d166614 p = 1) : d169210 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166609 q = 1) : d169205 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d166609, d169205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166609, d169205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15190 q selected
  have h2 (q : Pattern) (selected : d166610 q = 1) : d169206 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d166610, d169206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166610, d169206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166611 q = 1) : d169207 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d166611, d169207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166611, d169207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166612 q = 1) : d169208 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d166612, d169208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166612, d169208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166613 q = 1) : d169209 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d166613, d169209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166613, d169209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166614 q = 1) : d169210 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d166614, d169210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166614, d169210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15192 (p : Pattern) (selected : d13059 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (selected : d13058 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13059 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro15193 (p : Pattern) (selected : d166683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136105 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6391 q selected
  have h2 (q : Pattern) (selected : d136106 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166679 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15192 q selected
  have h4 (q : Pattern) (selected : d166680 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166681 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136107 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6392 q selected
  have h7 (q : Pattern) (selected : d136108 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136110 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d166682 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166683 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15194 (p : Pattern) (selected : d166689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15193 q selected
    | true =>
      simp only [d166684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166685 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136117 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11904 q selected
    | true =>
      simp only [d136117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136118 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166686 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166687 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166688 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166689 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15195 (p : Pattern) (selected : d166701 p = 1) : d169217 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166651 q = 1) : d166651 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d166657 q = 1) : d166657 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d166678 q = 1) : d166678 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d166690 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15194 q selected
    | true =>
      simp only [d166690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11906 q selected
  have h5 (q : Pattern) (selected : d166691 q = 1) : d169213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166691, d169213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166691, d169213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166697 q = 1) : d166697 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d166698 q = 1) : d169214 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166698, d169214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166698, d169214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166699 q = 1) : d169215 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166699, d169215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166699, d169215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d166700 q = 1) : d169216 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166700, d169216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166700, d169216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166701 q = 1) : d169217 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166701, d169217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166701, d169217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro15196 (p : Pattern) (selected : d166714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15193 q selected
    | true =>
      simp only [d166684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166685 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136117 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11904 q selected
    | true =>
      simp only [d136117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136118 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166686 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166687 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166688 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166714 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15197 (p : Pattern) (selected : d166723 p = 1) : d169222 p = 1 := by
  have h0 (q : Pattern) (selected : d166651 q = 1) : d166651 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166657 q = 1) : d166657 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d166678 q = 1) : d166678 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d166690 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15194 q selected
    | true =>
      simp only [d166690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11906 q selected
  have h4 (q : Pattern) (selected : d166691 q = 1) : d169213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166691, d169213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166691, d169213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166697 q = 1) : d166697 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d166698 q = 1) : d169214 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166698, d169214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166698, d169214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166699 q = 1) : d169215 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166699, d169215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166699, d169215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166700 q = 1) : d169216 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166700, d169216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166700, d169216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d166706 q = 1) : d166706 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d166710 q = 1) : d166710 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d166713 q = 1) : d166713 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d166715 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15196 q selected
    | true =>
      simp only [d166715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11909 q selected
  have h13 (q : Pattern) (selected : d166716 q = 1) : d169218 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166716, d169218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166716, d169218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d166719 q = 1) : d166719 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d166720 q = 1) : d169219 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166720, d169219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d166720, d169219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d166721 q = 1) : d169220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166721, d169220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166721, d169220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d166722 q = 1) : d169221 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166722, d169221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166722, d169221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d166723 q = 1) : d169222 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166723, d169222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d166723, d169222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro15198 (p : Pattern) (selected : d166737 p = 1) : d169229 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166713 q = 1) : d166713 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d166715 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15196 q selected
    | true =>
      simp only [d166715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11909 q selected
  have h3 (q : Pattern) (selected : d166716 q = 1) : d169218 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166716, d169218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166716, d169218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166719 q = 1) : d166719 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d166720 q = 1) : d169219 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166720, d169219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166720, d169219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166735 q = 1) : d169227 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166735, d169227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166735, d169227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166736 q = 1) : d169228 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166736, d169228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166736, d169228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166737 q = 1) : d169229 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166737, d169229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166737, d169229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15199 (p : Pattern) (selected : d13213 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (selected : d13212 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13213 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro15200 (p : Pattern) (selected : d166771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136227 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6403 q selected
  have h2 (q : Pattern) (selected : d136228 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166767 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15199 q selected
  have h4 (q : Pattern) (selected : d166768 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166769 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136229 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6404 q selected
  have h7 (q : Pattern) (selected : d136230 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136232 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d166770 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166771 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15201 (p : Pattern) (selected : d166777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166772 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15200 q selected
    | true =>
      simp only [d166772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166773 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136239 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11913 q selected
    | true =>
      simp only [d136239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136240 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166775 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166776 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166777 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15202 (p : Pattern) (selected : d166793 p = 1) : d169239 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166766 q = 1) : d166766 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d166778 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15201 q selected
    | true =>
      simp only [d166778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11915 q selected
  have h3 (q : Pattern) (selected : d166779 q = 1) : d169235 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166779, d169235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166779, d169235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166789 q = 1) : d166789 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d166790 q = 1) : d169236 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166790, d169236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166790, d169236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166791 q = 1) : d169237 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166791, d169237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166791, d169237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166792 q = 1) : d169238 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166792, d169238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166792, d169238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166793 q = 1) : d169239 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166793, d169239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166793, d169239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15203 (p : Pattern) (selected : d166799 p = 1) : d169245 p = 1 := by
  have h0 (q : Pattern) (selected : d166645 q = 1) : d166645 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166724 q = 1) : d169223 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166724, d169223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15195 q selected
    | true =>
      simp only [d166724, d169223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15197 q selected
  have h2 (q : Pattern) (selected : d166731 q = 1) : d166731 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d166732 q = 1) : d169224 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166732, d169224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166732, d169224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d166733 q = 1) : d169225 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166733, d169225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166733, d169225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166734 q = 1) : d169226 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166734, d169226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166734, d169226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166738 q = 1) : d169230 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166738, d169230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166738, d169230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15198 q selected
  have h8 (q : Pattern) (selected : d136192 q = 1) : d136192 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d166739 q = 1) : d169231 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166739, d169231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166739, d169231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166740 q = 1) : d169232 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166740, d169232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166740, d169232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d166741 q = 1) : d169233 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166741, d169233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166741, d169233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d166742 q = 1) : d169234 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d166742, d169234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166742, d169234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d166794 q = 1) : d169240 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166794, d169240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166794, d169240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15202 q selected
  have h14 (q : Pattern) (selected : d136279 q = 1) : d136279 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d166795 q = 1) : d169241 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166795, d169241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d166795, d169241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d166796 q = 1) : d169242 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166796, d169242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d166796, d169242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d166797 q = 1) : d169243 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166797, d169243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d166797, d169243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d166798 q = 1) : d169244 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d166798, d169244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d166798, d169244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d166799 q = 1) : d169245 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d166799, d169245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d166799, d169245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro15204 (p : Pattern) (selected : d166805 p = 1) : d169251 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166800 q = 1) : d169246 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d166800, d169246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166800, d169246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15203 q selected
  have h2 (q : Pattern) (selected : d166801 q = 1) : d169247 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d166801, d169247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166801, d169247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166802 q = 1) : d169248 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d166802, d169248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166802, d169248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166803 q = 1) : d169249 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d166803, d169249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166803, d169249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166804 q = 1) : d169250 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d166804, d169250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166804, d169250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166805 q = 1) : d169251 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d166805, d169251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166805, d169251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15205 (p : Pattern) (selected : d13385 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (selected : d13384 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13385 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro15206 (p : Pattern) (selected : d166875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136364 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6413 q selected
  have h2 (q : Pattern) (selected : d136365 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166871 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15205 q selected
  have h4 (q : Pattern) (selected : d166872 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166873 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6414 q selected
  have h7 (q : Pattern) (selected : d136367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136369 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d166874 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166875 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15207 (p : Pattern) (selected : d166881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166876 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15206 q selected
    | true =>
      simp only [d166876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166877 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11920 q selected
    | true =>
      simp only [d136376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166878 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166879 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166880 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166881 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15208 (p : Pattern) (selected : d166893 p = 1) : d169259 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166843 q = 1) : d166843 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d166849 q = 1) : d166849 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d166870 q = 1) : d166870 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d166882 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15207 q selected
    | true =>
      simp only [d166882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11922 q selected
  have h5 (q : Pattern) (selected : d166883 q = 1) : d169255 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166883, d169255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166883, d169255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166889 q = 1) : d166889 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d166890 q = 1) : d169256 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166890, d169256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166890, d169256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166891 q = 1) : d169257 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166891, d169257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166891, d169257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d166892 q = 1) : d169258 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166892, d169258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166892, d169258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166893 q = 1) : d169259 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166893, d169259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166893, d169259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro15209 (p : Pattern) (selected : d166906 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166876 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15206 q selected
    | true =>
      simp only [d166876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166877 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11920 q selected
    | true =>
      simp only [d136376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166878 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166879 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166880 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166906 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15210 (p : Pattern) (selected : d166915 p = 1) : d169264 p = 1 := by
  have h0 (q : Pattern) (selected : d166843 q = 1) : d166843 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166849 q = 1) : d166849 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d166870 q = 1) : d166870 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d166882 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15207 q selected
    | true =>
      simp only [d166882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11922 q selected
  have h4 (q : Pattern) (selected : d166883 q = 1) : d169255 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166883, d169255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166883, d169255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166889 q = 1) : d166889 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d166890 q = 1) : d169256 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166890, d169256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166890, d169256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166891 q = 1) : d169257 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166891, d169257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166891, d169257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166892 q = 1) : d169258 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166892, d169258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166892, d169258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d166898 q = 1) : d166898 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d166902 q = 1) : d166902 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d166905 q = 1) : d166905 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d166907 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15209 q selected
    | true =>
      simp only [d166907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11925 q selected
  have h13 (q : Pattern) (selected : d166908 q = 1) : d169260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166908, d169260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d166908, d169260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d166911 q = 1) : d166911 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d166912 q = 1) : d169261 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166912, d169261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d166912, d169261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d166913 q = 1) : d169262 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166913, d169262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166913, d169262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d166914 q = 1) : d169263 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166914, d169263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166914, d169263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d166915 q = 1) : d169264 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166915, d169264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d166915, d169264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro15211 (p : Pattern) (selected : d166929 p = 1) : d169271 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166905 q = 1) : d166905 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d166907 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15209 q selected
    | true =>
      simp only [d166907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11925 q selected
  have h3 (q : Pattern) (selected : d166908 q = 1) : d169260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166908, d169260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166908, d169260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166911 q = 1) : d166911 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d166912 q = 1) : d169261 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166912, d169261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166912, d169261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166927 q = 1) : d169269 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166927, d169269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166927, d169269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166928 q = 1) : d169270 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166928, d169270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166928, d169270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166929 q = 1) : d169271 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166929, d169271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166929, d169271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15212 (p : Pattern) (selected : d13539 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (selected : d13538 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13539 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro15213 (p : Pattern) (selected : d166963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6425 q selected
  have h2 (q : Pattern) (selected : d136487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166959 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d166959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15212 q selected
  have h4 (q : Pattern) (selected : d166960 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d166960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166961 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d166961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136488 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6426 q selected
  have h7 (q : Pattern) (selected : d136489 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136491 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d166962 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d166962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166963 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d166963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15214 (p : Pattern) (selected : d166969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166964 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d166964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15213 q selected
    | true =>
      simp only [d166964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d166965 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d166965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136498 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11929 q selected
    | true =>
      simp only [d136498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136499 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166966 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d166966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166967 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d166967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166968 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d166968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166969 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d166969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15215 (p : Pattern) (selected : d166985 p = 1) : d169281 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166958 q = 1) : d166958 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d166970 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d166970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15214 q selected
    | true =>
      simp only [d166970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11931 q selected
  have h3 (q : Pattern) (selected : d166971 q = 1) : d169277 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d166971, d169277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166971, d169277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166981 q = 1) : d166981 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d166982 q = 1) : d169278 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d166982, d169278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166982, d169278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166983 q = 1) : d169279 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d166983, d169279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166983, d169279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166984 q = 1) : d169280 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d166984, d169280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166984, d169280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d166985 q = 1) : d169281 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d166985, d169281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166985, d169281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15216 (p : Pattern) (selected : d166991 p = 1) : d169287 p = 1 := by
  have h0 (q : Pattern) (selected : d166837 q = 1) : d166837 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166916 q = 1) : d169265 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166916, d169265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15208 q selected
    | true =>
      simp only [d166916, d169265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15210 q selected
  have h2 (q : Pattern) (selected : d166923 q = 1) : d166923 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d166924 q = 1) : d169266 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166924, d169266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166924, d169266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d166925 q = 1) : d169267 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166925, d169267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166925, d169267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166926 q = 1) : d169268 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166926, d169268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166926, d169268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166930 q = 1) : d169272 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166930, d169272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166930, d169272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15211 q selected
  have h8 (q : Pattern) (selected : d136451 q = 1) : d136451 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d166931 q = 1) : d169273 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166931, d169273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166931, d169273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d166932 q = 1) : d169274 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166932, d169274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d166932, d169274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d166933 q = 1) : d169275 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166933, d169275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d166933, d169275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d166934 q = 1) : d169276 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d166934, d169276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d166934, d169276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d166986 q = 1) : d169282 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d166986, d169282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166986, d169282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15215 q selected
  have h14 (q : Pattern) (selected : d136538 q = 1) : d136538 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d166987 q = 1) : d169283 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d166987, d169283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d166987, d169283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d166988 q = 1) : d169284 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d166988, d169284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d166988, d169284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d166989 q = 1) : d169285 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d166989, d169285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d166989, d169285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d166990 q = 1) : d169286 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d166990, d169286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d166990, d169286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d166991 q = 1) : d169287 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d166991, d169287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d166991, d169287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro15217 (p : Pattern) (selected : d166997 p = 1) : d169293 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d166992 q = 1) : d169288 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d166992, d169288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166992, d169288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15216 q selected
  have h2 (q : Pattern) (selected : d166993 q = 1) : d169289 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d166993, d169289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166993, d169289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d166994 q = 1) : d169290 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d166994, d169290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166994, d169290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166995 q = 1) : d169291 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d166995, d169291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166995, d169291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d166996 q = 1) : d169292 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d166996, d169292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166996, d169292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166997 q = 1) : d169293 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d166997, d169293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166997, d169293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15218 (p : Pattern) (selected : d13712 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (selected : d13711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13712 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro15219 (p : Pattern) (selected : d167068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136624 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6435 q selected
  have h2 (q : Pattern) (selected : d136625 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167064 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15218 q selected
  have h4 (q : Pattern) (selected : d167065 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167066 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136626 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6436 q selected
  have h7 (q : Pattern) (selected : d136627 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136629 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d167067 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d167068 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d167068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15220 (p : Pattern) (selected : d167074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d167069 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15219 q selected
    | true =>
      simp only [d167069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167070 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136636 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11936 q selected
    | true =>
      simp only [d136636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136637 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167071 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167072 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d167073 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d167074 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15221 (p : Pattern) (selected : d167086 p = 1) : d169302 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d167036 q = 1) : d167036 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d167042 q = 1) : d167042 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d167063 q = 1) : d167063 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d167075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15220 q selected
    | true =>
      simp only [d167075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11938 q selected
  have h5 (q : Pattern) (selected : d167076 q = 1) : d169298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167076, d169298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167076, d169298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167082 q = 1) : d167082 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d167083 q = 1) : d169299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167083, d169299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167083, d169299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d167084 q = 1) : d169300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167084, d169300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167084, d169300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d167085 q = 1) : d169301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167085, d169301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167085, d169301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d167086 q = 1) : d169302 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167086, d169302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167086, d169302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro15222 (p : Pattern) (selected : d167099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d167069 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15219 q selected
    | true =>
      simp only [d167069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167070 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136636 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11936 q selected
    | true =>
      simp only [d136636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136637 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167071 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167072 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d167073 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d167099 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d167099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15223 (p : Pattern) (selected : d167108 p = 1) : d169307 p = 1 := by
  have h0 (q : Pattern) (selected : d167036 q = 1) : d167036 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d167042 q = 1) : d167042 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d167063 q = 1) : d167063 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d167075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15220 q selected
    | true =>
      simp only [d167075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11938 q selected
  have h4 (q : Pattern) (selected : d167076 q = 1) : d169298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167076, d169298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167076, d169298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167082 q = 1) : d167082 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d167083 q = 1) : d169299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167083, d169299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167083, d169299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d167084 q = 1) : d169300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167084, d169300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167084, d169300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d167085 q = 1) : d169301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167085, d169301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167085, d169301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d167091 q = 1) : d167091 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d167095 q = 1) : d167095 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d167098 q = 1) : d167098 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d167100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15222 q selected
    | true =>
      simp only [d167100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11941 q selected
  have h13 (q : Pattern) (selected : d167101 q = 1) : d169303 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167101, d169303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d167101, d169303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d167104 q = 1) : d167104 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d167105 q = 1) : d169304 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167105, d169304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d167105, d169304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d167106 q = 1) : d169305 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167106, d169305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d167106, d169305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d167107 q = 1) : d169306 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167107, d169306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d167107, d169306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d167108 q = 1) : d169307 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167108, d169307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d167108, d169307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro15224 (p : Pattern) (selected : d167122 p = 1) : d169314 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d167098 q = 1) : d167098 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d167100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15222 q selected
    | true =>
      simp only [d167100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11941 q selected
  have h3 (q : Pattern) (selected : d167101 q = 1) : d169303 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167101, d169303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167101, d169303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d167104 q = 1) : d167104 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d167105 q = 1) : d169304 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167105, d169304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167105, d169304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167120 q = 1) : d169312 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167120, d169312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167120, d169312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d167121 q = 1) : d169313 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167121, d169313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167121, d169313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d167122 q = 1) : d169314 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167122, d169314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167122, d169314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15225 (p : Pattern) (selected : d13866 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (selected : d13865 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13866 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro15226 (p : Pattern) (selected : d167156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136746 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6447 q selected
  have h2 (q : Pattern) (selected : d136747 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167152 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15225 q selected
  have h4 (q : Pattern) (selected : d167153 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167154 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136748 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6448 q selected
  have h7 (q : Pattern) (selected : d136749 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136751 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d167155 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d167156 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d167156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15227 (p : Pattern) (selected : d167162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d167157 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15226 q selected
    | true =>
      simp only [d167157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167158 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136758 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11945 q selected
    | true =>
      simp only [d136758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136759 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167159 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167160 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d167161 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d167162 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d167162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15228 (p : Pattern) (selected : d167178 p = 1) : d169324 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d167151 q = 1) : d167151 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d167163 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15227 q selected
    | true =>
      simp only [d167163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11947 q selected
  have h3 (q : Pattern) (selected : d167164 q = 1) : d169320 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167164, d169320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167164, d169320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d167174 q = 1) : d167174 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d167175 q = 1) : d169321 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167175, d169321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167175, d169321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167176 q = 1) : d169322 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167176, d169322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167176, d169322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d167177 q = 1) : d169323 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167177, d169323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167177, d169323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d167178 q = 1) : d169324 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167178, d169324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167178, d169324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15229 (p : Pattern) (selected : d167184 p = 1) : d169330 p = 1 := by
  have h0 (q : Pattern) (selected : d167030 q = 1) : d167030 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d167109 q = 1) : d169308 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167109, d169308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15221 q selected
    | true =>
      simp only [d167109, d169308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15223 q selected
  have h2 (q : Pattern) (selected : d167116 q = 1) : d167116 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d167117 q = 1) : d169309 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167117, d169309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167117, d169309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d167118 q = 1) : d169310 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167118, d169310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167118, d169310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167119 q = 1) : d169311 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167119, d169311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167119, d169311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d167123 q = 1) : d169315 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167123, d169315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167123, d169315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15224 q selected
  have h8 (q : Pattern) (selected : d136711 q = 1) : d136711 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d167124 q = 1) : d169316 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167124, d169316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d167124, d169316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d167125 q = 1) : d169317 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167125, d169317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d167125, d169317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d167126 q = 1) : d169318 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167126, d169318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d167126, d169318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d167127 q = 1) : d169319 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167127, d169319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167127, d169319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d167179 q = 1) : d169325 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167179, d169325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167179, d169325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15228 q selected
  have h14 (q : Pattern) (selected : d136798 q = 1) : d136798 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d167180 q = 1) : d169326 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167180, d169326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d167180, d169326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d167181 q = 1) : d169327 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167181, d169327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d167181, d169327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d167182 q = 1) : d169328 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167182, d169328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d167182, d169328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d167183 q = 1) : d169329 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167183, d169329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d167183, d169329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d167184 q = 1) : d169330 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d167184, d169330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d167184, d169330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro15230 (p : Pattern) (selected : d167190 p = 1) : d169336 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d167185 q = 1) : d169331 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d167185, d169331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167185, d169331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15229 q selected
  have h2 (q : Pattern) (selected : d167186 q = 1) : d169332 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d167186, d169332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167186, d169332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d167187 q = 1) : d169333 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d167187, d169333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167187, d169333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d167188 q = 1) : d169334 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d167188, d169334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167188, d169334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d167189 q = 1) : d169335 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d167189, d169335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167189, d169335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d167190 q = 1) : d169336 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d167190, d169336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d167190, d169336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15231 (p : Pattern) (selected : d167196 p = 1) : d169342 p = 1 := by
  have h0 (q : Pattern) (selected : d166534 q = 1) : d169171 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d166534, d169171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11875 q selected
    | true =>
      simp only [d166534, d169171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15185 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d166615 q = 1) : d169211 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d166615, d169211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166615, d169211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15191 q selected
  have h3 (q : Pattern) (selected : d166616 q = 1) : d169212 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d166616, d169212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d166616, d169212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d166806 q = 1) : d169252 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d166806, d169252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166806, d169252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15204 q selected
  have h5 (q : Pattern) (selected : d166807 q = 1) : d169253 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d166807, d169253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166807, d169253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166808 q = 1) : d169254 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d166808, d169254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d166808, d169254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d166998 q = 1) : d169294 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d166998, d169294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166998, d169294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15217 q selected
  have h8 (q : Pattern) (selected : d166999 q = 1) : d169295 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d166999, d169295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d166999, d169295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d167000 q = 1) : d169296 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d167000, d169296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167000, d169296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d167001 q = 1) : d169297 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d167001, d169297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167001, d169297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d167191 q = 1) : d169337 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d167191, d169337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167191, d169337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15230 q selected
  have h12 (q : Pattern) (selected : d167192 q = 1) : d169338 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d167192, d169338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167192, d169338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d167193 q = 1) : d169339 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d167193, d169339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167193, d169339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d167194 q = 1) : d169340 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d167194, d169340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167194, d169340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d167195 q = 1) : d169341 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d167195, d169341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d167195, d169341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d167196 q = 1) : d169342 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d167196, d169342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d167196, d169342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro15232 (p : Pattern) (selected : d167202 p = 1) : d169348 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d167197 q = 1) : d169343 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d167197, d169343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15231 q selected
    | true =>
      simp only [d167197, d169343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167198 q = 1) : d169344 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d167198, d169344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167198, d169344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d167199 q = 1) : d169345 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d167199, d169345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167199, d169345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167200 q = 1) : d169346 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d167200, d169346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167200, d169346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167201 q = 1) : d169347 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d167201, d169347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167201, d169347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d167202 q = 1) : d169348 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d167202, d169348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167202, d169348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15233 (p : Pattern) (selected : d167208 p = 1) : d169354 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d167203 q = 1) : d169349 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d167203, d169349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15232 q selected
    | true =>
      simp only [d167203, d169349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167204 q = 1) : d169350 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d167204, d169350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167204, d169350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d167205 q = 1) : d169351 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d167205, d169351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167205, d169351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167206 q = 1) : d169352 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d167206, d169352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167206, d169352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167207 q = 1) : d169353 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d167207, d169353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167207, d169353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d167208 q = 1) : d169354 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d167208, d169354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167208, d169354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15234 (p : Pattern) (selected : d167214 p = 1) : d169360 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d167209 q = 1) : d169355 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d167209, d169355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15233 q selected
    | true =>
      simp only [d167209, d169355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167210 q = 1) : d169356 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d167210, d169356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167210, d169356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d167211 q = 1) : d169357 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d167211, d169357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167211, d169357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167212 q = 1) : d169358 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d167212, d169358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167212, d169358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167213 q = 1) : d169359 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d167213, d169359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167213, d169359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d167214 q = 1) : d169360 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d167214, d169360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167214, d169360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15235 (p : Pattern) (selected : d167220 p = 1) : d169366 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d167215 q = 1) : d169361 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d167215, d169361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15234 q selected
    | true =>
      simp only [d167215, d169361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167216 q = 1) : d169362 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d167216, d169362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167216, d169362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d167217 q = 1) : d169363 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d167217, d169363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167217, d169363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167218 q = 1) : d169364 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d167218, d169364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167218, d169364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167219 q = 1) : d169365 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d167219, d169365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167219, d169365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d167220 q = 1) : d169366 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d167220, d169366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167220, d169366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15236 (p : Pattern) (selected : d167226 p = 1) : d169372 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d167221 q = 1) : d169367 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d167221, d169367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15235 q selected
    | true =>
      simp only [d167221, d169367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167222 q = 1) : d169368 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d167222, d169368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167222, d169368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d167223 q = 1) : d169369 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d167223, d169369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167223, d169369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167224 q = 1) : d169370 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d167224, d169370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167224, d169370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167225 q = 1) : d169371 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d167225, d169371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167225, d169371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d167226 q = 1) : d169372 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d167226, d169372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167226, d169372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15237 (p : Pattern) (selected : d167232 p = 1) : d169378 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d167227 q = 1) : d169373 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d167227, d169373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15236 q selected
    | true =>
      simp only [d167227, d169373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167228 q = 1) : d169374 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d167228, d169374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167228, d169374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d167229 q = 1) : d169375 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d167229, d169375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167229, d169375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167230 q = 1) : d169376 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d167230, d169376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167230, d169376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167231 q = 1) : d169377 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d167231, d169377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167231, d169377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d167232 q = 1) : d169378 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d167232, d169378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167232, d169378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15238 (p : Pattern) (selected : d167238 p = 1) : d169384 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d167233 q = 1) : d169379 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d167233, d169379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15237 q selected
    | true =>
      simp only [d167233, d169379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d167234 q = 1) : d169380 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d167234, d169380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d167234, d169380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d167235 q = 1) : d169381 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d167235, d169381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d167235, d169381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167236 q = 1) : d169382 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d167236, d169382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167236, d169382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d167237 q = 1) : d169383 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d167237, d169383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d167237, d169383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d167238 q = 1) : d169384 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d167238, d169384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d167238, d169384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15239 (p : Pattern) (selected : d15966 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d319 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro693 q selected
    | true =>
      simp only [d319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d320 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d321 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d322 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d139 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro663 q selected
    | true =>
      simp only [d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d140 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d141 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d323 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9382 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10492 q selected
    | true =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d9384 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d9384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d12493 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d12494 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d12494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d25 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d26 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d27 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d28 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d12495 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d12495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d15966 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro15240 (p : Pattern) (selected : d15972 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15967 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15239 q selected
    | true =>
      simp only [d15967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro664 q selected
  have h2 (q : Pattern) (selected : d15968 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15969 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d145 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro664 q selected
    | true =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro646 q selected
  have h5 (q : Pattern) (selected : d146 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d147 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15970 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d31 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro646 q selected
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d32 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d33 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d148 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15971 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15972 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro15241 (p : Pattern) (selected : d15978 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15973 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15240 q selected
    | true =>
      simp only [d15973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15974 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d151 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro665 q selected
    | true =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15975 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15976 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15977 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15978 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15242 (p : Pattern) (selected : d15984 p = 2) : d284 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d297 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro690 q selected
    | true =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro660 q selected
  have h2 (q : Pattern) (selected : d298 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d299 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d304 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro691 q selected
    | true =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro661 q selected
  have h6 (q : Pattern) (selected : d305 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d306 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15979 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15241 q selected
    | true =>
      simp only [d15979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro666 q selected
  have h9 (q : Pattern) (selected : d368 q = 2) : d157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368, d157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro701 q selected
    | true =>
      simp only [d368, d157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro671 q selected
  have h10 (q : Pattern) (selected : d15980 q = 2) : d280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15980, d280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15980, d280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4737 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3807 q selected
    | true =>
      simp only [d4737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d5350 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d5350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d15981 q = 2) : d281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15981, d281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15981, d281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d15982 q = 2) : d282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15982, d282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15982, d282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d15983 q = 2) : d283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15983, d283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15983, d283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d15984 q = 2) : d284 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15984, d284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15984, d284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro15243 (p : Pattern) (selected : d15985 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15973 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15240 q selected
    | true =>
      simp only [d15973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15974 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d151 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro665 q selected
    | true =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15975 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15976 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15977 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15985 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15244 (p : Pattern) (selected : d15991 p = 2) : d291 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d297 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro690 q selected
    | true =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro660 q selected
  have h2 (q : Pattern) (selected : d298 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d299 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d304 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro691 q selected
    | true =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro661 q selected
  have h6 (q : Pattern) (selected : d305 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d306 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15979 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15241 q selected
    | true =>
      simp only [d15979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro666 q selected
  have h9 (q : Pattern) (selected : d368 q = 2) : d157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368, d157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro701 q selected
    | true =>
      simp only [d368, d157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro671 q selected
  have h10 (q : Pattern) (selected : d15980 q = 2) : d280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15980, d280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15980, d280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4737 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3807 q selected
    | true =>
      simp only [d4737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d5350 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d5350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d15981 q = 2) : d281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15981, d281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15981, d281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d15982 q = 2) : d282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15982, d282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15982, d282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d15983 q = 2) : d283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15983, d283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15983, d283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d377 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro703 q selected
    | true =>
      simp only [d377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro673 q selected
  have h17 (q : Pattern) (selected : d378 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d379 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d380 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d382 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro704 q selected
    | true =>
      simp only [d382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro674 q selected
  have h21 (q : Pattern) (selected : d383 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d384 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d15986 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15243 q selected
    | true =>
      simp only [d15986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro675 q selected
  have h24 (q : Pattern) (selected : d388 q = 2) : d204 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d388, d204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro706 q selected
    | true =>
      simp only [d388, d204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro676 q selected
  have h25 (q : Pattern) (selected : d15987 q = 2) : d287 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15987, d287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d15987, d287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d5356 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4358 q selected
    | true =>
      simp only [d5356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d5357 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d5357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d15988 q = 2) : d288 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15988, d288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d15988, d288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d15989 q = 2) : d289 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15989, d289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d15989, d289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d15990 q = 2) : d290 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15990, d290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d15990, d290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d15991 q = 2) : d291 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15991, d291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d15991, d291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro15245 (p : Pattern) (selected : d15998 p = 2) : d53655 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15986 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15243 q selected
    | true =>
      simp only [d15986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro675 q selected
  have h2 (q : Pattern) (selected : d388 q = 2) : d204 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d388, d204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro706 q selected
    | true =>
      simp only [d388, d204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro676 q selected
  have h3 (q : Pattern) (selected : d15987 q = 2) : d287 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15987, d287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15987, d287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5356 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4358 q selected
    | true =>
      simp only [d5356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d5357 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d5357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15988 q = 2) : d288 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15988, d288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15988, d288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15996 q = 2) : d289 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15996, d289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15996, d289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15997 q = 2) : d290 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15997, d290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15997, d290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d15998 q = 2) : d53655 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15998, d53655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15998, d53655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15246 (p : Pattern) (selected : d16004 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d412 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro693 q selected
  have h2 (q : Pattern) (selected : d319 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro693 q selected
    | true =>
      simp only [d319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d413 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d320 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d414 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d415 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro663 q selected
  have h8 (q : Pattern) (selected : d139 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro663 q selected
    | true =>
      simp only [d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d140 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d229 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d416 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d12599 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10492 q selected
  have h15 (q : Pattern) (selected : d9382 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10492 q selected
    | true =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d12600 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d12600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d9384 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d9384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d12601 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d12601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d12602 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d12602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d66 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
  have h21 (q : Pattern) (selected : d25 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d67 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d26 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d68 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d69 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d12603 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d12603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d16004 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d16004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro15247 (p : Pattern) (selected : d16010 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d16005 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15246 q selected
    | true =>
      simp only [d16005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro680 q selected
  have h2 (q : Pattern) (selected : d16006 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d16007 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro680 q selected
    | true =>
      simp only [d232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro653 q selected
  have h5 (q : Pattern) (selected : d233 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d234 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d16008 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d72 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro653 q selected
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d73 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d74 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d235 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d16009 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d16009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d16010 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d16010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro15248 (p : Pattern) (selected : d16016 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d16011 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15247 q selected
    | true =>
      simp only [d16011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d16012 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d238 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro681 q selected
    | true =>
      simp only [d238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d239 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d16013 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d16013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d16014 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d16014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d16015 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d16015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d16016 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d16016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15249 (p : Pattern) (selected : d16022 p = 2) : d53665 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d16017 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15248 q selected
    | true =>
      simp only [d16017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro682 q selected
  have h2 (q : Pattern) (selected : d449 q = 2) : d244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d449, d244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro716 q selected
    | true =>
      simp only [d449, d244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro685 q selected
  have h3 (q : Pattern) (selected : d16018 q = 2) : d53661 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16018, d53661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d16018, d53661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5378 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4361 q selected
    | true =>
      simp only [d5378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d5379 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d5379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16019 q = 2) : d53662 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16019, d53662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16019, d53662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d16020 q = 2) : d53663 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16020, d53663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16020, d53663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d16021 q = 2) : d53664 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16021, d53664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16021, d53664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d16022 q = 2) : d53665 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16022, d53665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16022, d53665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
end NetHack.Soko22Hazard87
